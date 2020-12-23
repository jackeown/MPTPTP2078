%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:13 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :  143 (2557 expanded)
%              Number of clauses        :   89 ( 800 expanded)
%              Number of leaves         :   14 ( 670 expanded)
%              Depth                    :   30
%              Number of atoms          :  452 (14605 expanded)
%              Number of equality atoms :  128 (1034 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f22])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f28])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f48])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f24])).

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,
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

fof(f33,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f32,f31,f30])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f49])).

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

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f47])).

cnf(c_11,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_553,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_554,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_1861,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_555,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1992,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1993,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1992])).

cnf(c_2194,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1861,c_27,c_555,c_1993])).

cnf(c_2195,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2194])).

cnf(c_1870,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_173,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_288,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_6,c_4])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_6,c_5,c_4])).

cnf(c_293,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_310,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X3 != X1
    | k1_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_173,c_293])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_1868,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_2656,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1870,c_1868])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1875,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2717,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | m1_subset_1(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2656,c_1875])).

cnf(c_2725,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_2717])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_370,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_371,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_487,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_371,c_20])).

cnf(c_488,plain,
    ( ~ v1_funct_2(sK4,sK2,X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_1865,plain,
    ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | v1_funct_2(sK4,sK2,X0) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_2509,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1870,c_1865])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_681,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | k3_funct_2(sK2,X1,sK4,X0) = k1_funct_1(sK4,X0)
    | sK4 != sK4
    | sK3 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_488])).

cnf(c_682,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_686,plain,
    ( ~ m1_subset_1(X0,sK2)
    | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_682,c_18])).

cnf(c_688,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_2512,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2509,c_688])).

cnf(c_2833,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),X0,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2725,c_2512])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1872,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2896,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),X0,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4))
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2833,c_1872])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
    | ~ m1_subset_1(X0,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1871,plain,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2946,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),sK1) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2896,c_1871])).

cnf(c_2053,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2069,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2053])).

cnf(c_2951,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),sK1) = iProver_top
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2946,c_2069,c_2725])).

cnf(c_2952,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2951])).

cnf(c_10,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_568,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_569,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_1860,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_569])).

cnf(c_570,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_569])).

cnf(c_2096,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1860,c_27,c_570,c_1993])).

cnf(c_2097,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2096])).

cnf(c_2959,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2952,c_2097])).

cnf(c_3030,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2959,c_1872])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1873,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3031,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3030,c_1873])).

cnf(c_2266,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1870,c_1872])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_171,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k2_relset_1(sK2,sK3,sK4) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_171,c_16])).

cnf(c_323,plain,
    ( ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_1867,plain,
    ( m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_2401,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2266,c_1867])).

cnf(c_3096,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3031,c_2401])).

cnf(c_3101,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),sK1,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) ),
    inference(superposition,[status(thm)],[c_2833,c_3096])).

cnf(c_3275,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)),sK1) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3101,c_1871])).

cnf(c_12,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_538,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_539,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_1862,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_540,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_2025,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
    | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1862,c_27,c_540,c_1993])).

cnf(c_2026,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2025])).

cnf(c_3397,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),sK1) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3275,c_2026])).

cnf(c_3396,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3275,c_2097])).

cnf(c_3409,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3397,c_2401,c_3031,c_3396])).

cnf(c_3414,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2725,c_3409])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3414,c_3031,c_2401])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.91/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.00  
% 2.91/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.91/1.00  
% 2.91/1.00  ------  iProver source info
% 2.91/1.00  
% 2.91/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.91/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.91/1.00  git: non_committed_changes: false
% 2.91/1.00  git: last_make_outside_of_git: false
% 2.91/1.00  
% 2.91/1.00  ------ 
% 2.91/1.00  
% 2.91/1.00  ------ Input Options
% 2.91/1.00  
% 2.91/1.00  --out_options                           all
% 2.91/1.00  --tptp_safe_out                         true
% 2.91/1.00  --problem_path                          ""
% 2.91/1.00  --include_path                          ""
% 2.91/1.00  --clausifier                            res/vclausify_rel
% 2.91/1.00  --clausifier_options                    --mode clausify
% 2.91/1.00  --stdin                                 false
% 2.91/1.00  --stats_out                             all
% 2.91/1.00  
% 2.91/1.00  ------ General Options
% 2.91/1.00  
% 2.91/1.00  --fof                                   false
% 2.91/1.00  --time_out_real                         305.
% 2.91/1.00  --time_out_virtual                      -1.
% 2.91/1.00  --symbol_type_check                     false
% 2.91/1.00  --clausify_out                          false
% 2.91/1.00  --sig_cnt_out                           false
% 2.91/1.00  --trig_cnt_out                          false
% 2.91/1.00  --trig_cnt_out_tolerance                1.
% 2.91/1.00  --trig_cnt_out_sk_spl                   false
% 2.91/1.00  --abstr_cl_out                          false
% 2.91/1.00  
% 2.91/1.00  ------ Global Options
% 2.91/1.00  
% 2.91/1.00  --schedule                              default
% 2.91/1.00  --add_important_lit                     false
% 2.91/1.00  --prop_solver_per_cl                    1000
% 2.91/1.00  --min_unsat_core                        false
% 2.91/1.00  --soft_assumptions                      false
% 2.91/1.00  --soft_lemma_size                       3
% 2.91/1.00  --prop_impl_unit_size                   0
% 2.91/1.00  --prop_impl_unit                        []
% 2.91/1.00  --share_sel_clauses                     true
% 2.91/1.00  --reset_solvers                         false
% 2.91/1.00  --bc_imp_inh                            [conj_cone]
% 2.91/1.00  --conj_cone_tolerance                   3.
% 2.91/1.00  --extra_neg_conj                        none
% 2.91/1.00  --large_theory_mode                     true
% 2.91/1.00  --prolific_symb_bound                   200
% 2.91/1.00  --lt_threshold                          2000
% 2.91/1.00  --clause_weak_htbl                      true
% 2.91/1.00  --gc_record_bc_elim                     false
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing Options
% 2.91/1.00  
% 2.91/1.00  --preprocessing_flag                    true
% 2.91/1.00  --time_out_prep_mult                    0.1
% 2.91/1.00  --splitting_mode                        input
% 2.91/1.00  --splitting_grd                         true
% 2.91/1.00  --splitting_cvd                         false
% 2.91/1.00  --splitting_cvd_svl                     false
% 2.91/1.00  --splitting_nvd                         32
% 2.91/1.00  --sub_typing                            true
% 2.91/1.00  --prep_gs_sim                           true
% 2.91/1.00  --prep_unflatten                        true
% 2.91/1.00  --prep_res_sim                          true
% 2.91/1.00  --prep_upred                            true
% 2.91/1.00  --prep_sem_filter                       exhaustive
% 2.91/1.00  --prep_sem_filter_out                   false
% 2.91/1.00  --pred_elim                             true
% 2.91/1.00  --res_sim_input                         true
% 2.91/1.00  --eq_ax_congr_red                       true
% 2.91/1.00  --pure_diseq_elim                       true
% 2.91/1.00  --brand_transform                       false
% 2.91/1.00  --non_eq_to_eq                          false
% 2.91/1.00  --prep_def_merge                        true
% 2.91/1.00  --prep_def_merge_prop_impl              false
% 2.91/1.00  --prep_def_merge_mbd                    true
% 2.91/1.00  --prep_def_merge_tr_red                 false
% 2.91/1.00  --prep_def_merge_tr_cl                  false
% 2.91/1.00  --smt_preprocessing                     true
% 2.91/1.00  --smt_ac_axioms                         fast
% 2.91/1.00  --preprocessed_out                      false
% 2.91/1.00  --preprocessed_stats                    false
% 2.91/1.00  
% 2.91/1.00  ------ Abstraction refinement Options
% 2.91/1.00  
% 2.91/1.00  --abstr_ref                             []
% 2.91/1.00  --abstr_ref_prep                        false
% 2.91/1.00  --abstr_ref_until_sat                   false
% 2.91/1.00  --abstr_ref_sig_restrict                funpre
% 2.91/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.91/1.00  --abstr_ref_under                       []
% 2.91/1.00  
% 2.91/1.00  ------ SAT Options
% 2.91/1.00  
% 2.91/1.00  --sat_mode                              false
% 2.91/1.00  --sat_fm_restart_options                ""
% 2.91/1.00  --sat_gr_def                            false
% 2.91/1.00  --sat_epr_types                         true
% 2.91/1.00  --sat_non_cyclic_types                  false
% 2.91/1.00  --sat_finite_models                     false
% 2.91/1.00  --sat_fm_lemmas                         false
% 2.91/1.00  --sat_fm_prep                           false
% 2.91/1.00  --sat_fm_uc_incr                        true
% 2.91/1.00  --sat_out_model                         small
% 2.91/1.00  --sat_out_clauses                       false
% 2.91/1.00  
% 2.91/1.00  ------ QBF Options
% 2.91/1.00  
% 2.91/1.00  --qbf_mode                              false
% 2.91/1.00  --qbf_elim_univ                         false
% 2.91/1.00  --qbf_dom_inst                          none
% 2.91/1.00  --qbf_dom_pre_inst                      false
% 2.91/1.00  --qbf_sk_in                             false
% 2.91/1.00  --qbf_pred_elim                         true
% 2.91/1.00  --qbf_split                             512
% 2.91/1.00  
% 2.91/1.00  ------ BMC1 Options
% 2.91/1.00  
% 2.91/1.00  --bmc1_incremental                      false
% 2.91/1.00  --bmc1_axioms                           reachable_all
% 2.91/1.00  --bmc1_min_bound                        0
% 2.91/1.00  --bmc1_max_bound                        -1
% 2.91/1.00  --bmc1_max_bound_default                -1
% 2.91/1.00  --bmc1_symbol_reachability              true
% 2.91/1.00  --bmc1_property_lemmas                  false
% 2.91/1.00  --bmc1_k_induction                      false
% 2.91/1.00  --bmc1_non_equiv_states                 false
% 2.91/1.00  --bmc1_deadlock                         false
% 2.91/1.00  --bmc1_ucm                              false
% 2.91/1.00  --bmc1_add_unsat_core                   none
% 2.91/1.00  --bmc1_unsat_core_children              false
% 2.91/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.91/1.00  --bmc1_out_stat                         full
% 2.91/1.00  --bmc1_ground_init                      false
% 2.91/1.00  --bmc1_pre_inst_next_state              false
% 2.91/1.00  --bmc1_pre_inst_state                   false
% 2.91/1.00  --bmc1_pre_inst_reach_state             false
% 2.91/1.00  --bmc1_out_unsat_core                   false
% 2.91/1.00  --bmc1_aig_witness_out                  false
% 2.91/1.00  --bmc1_verbose                          false
% 2.91/1.00  --bmc1_dump_clauses_tptp                false
% 2.91/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.91/1.00  --bmc1_dump_file                        -
% 2.91/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.91/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.91/1.00  --bmc1_ucm_extend_mode                  1
% 2.91/1.00  --bmc1_ucm_init_mode                    2
% 2.91/1.00  --bmc1_ucm_cone_mode                    none
% 2.91/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.91/1.00  --bmc1_ucm_relax_model                  4
% 2.91/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.91/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.91/1.00  --bmc1_ucm_layered_model                none
% 2.91/1.00  --bmc1_ucm_max_lemma_size               10
% 2.91/1.00  
% 2.91/1.00  ------ AIG Options
% 2.91/1.00  
% 2.91/1.00  --aig_mode                              false
% 2.91/1.00  
% 2.91/1.00  ------ Instantiation Options
% 2.91/1.00  
% 2.91/1.00  --instantiation_flag                    true
% 2.91/1.00  --inst_sos_flag                         false
% 2.91/1.00  --inst_sos_phase                        true
% 2.91/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.91/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.91/1.00  --inst_lit_sel_side                     num_symb
% 2.91/1.00  --inst_solver_per_active                1400
% 2.91/1.00  --inst_solver_calls_frac                1.
% 2.91/1.00  --inst_passive_queue_type               priority_queues
% 2.91/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.91/1.00  --inst_passive_queues_freq              [25;2]
% 2.91/1.00  --inst_dismatching                      true
% 2.91/1.00  --inst_eager_unprocessed_to_passive     true
% 2.91/1.00  --inst_prop_sim_given                   true
% 2.91/1.00  --inst_prop_sim_new                     false
% 2.91/1.00  --inst_subs_new                         false
% 2.91/1.00  --inst_eq_res_simp                      false
% 2.91/1.00  --inst_subs_given                       false
% 2.91/1.00  --inst_orphan_elimination               true
% 2.91/1.00  --inst_learning_loop_flag               true
% 2.91/1.00  --inst_learning_start                   3000
% 2.91/1.00  --inst_learning_factor                  2
% 2.91/1.00  --inst_start_prop_sim_after_learn       3
% 2.91/1.00  --inst_sel_renew                        solver
% 2.91/1.00  --inst_lit_activity_flag                true
% 2.91/1.00  --inst_restr_to_given                   false
% 2.91/1.00  --inst_activity_threshold               500
% 2.91/1.00  --inst_out_proof                        true
% 2.91/1.00  
% 2.91/1.00  ------ Resolution Options
% 2.91/1.00  
% 2.91/1.00  --resolution_flag                       true
% 2.91/1.00  --res_lit_sel                           adaptive
% 2.91/1.00  --res_lit_sel_side                      none
% 2.91/1.00  --res_ordering                          kbo
% 2.91/1.00  --res_to_prop_solver                    active
% 2.91/1.00  --res_prop_simpl_new                    false
% 2.91/1.00  --res_prop_simpl_given                  true
% 2.91/1.00  --res_passive_queue_type                priority_queues
% 2.91/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.91/1.00  --res_passive_queues_freq               [15;5]
% 2.91/1.00  --res_forward_subs                      full
% 2.91/1.00  --res_backward_subs                     full
% 2.91/1.00  --res_forward_subs_resolution           true
% 2.91/1.00  --res_backward_subs_resolution          true
% 2.91/1.00  --res_orphan_elimination                true
% 2.91/1.00  --res_time_limit                        2.
% 2.91/1.00  --res_out_proof                         true
% 2.91/1.00  
% 2.91/1.00  ------ Superposition Options
% 2.91/1.00  
% 2.91/1.00  --superposition_flag                    true
% 2.91/1.00  --sup_passive_queue_type                priority_queues
% 2.91/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.91/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.91/1.00  --demod_completeness_check              fast
% 2.91/1.00  --demod_use_ground                      true
% 2.91/1.00  --sup_to_prop_solver                    passive
% 2.91/1.00  --sup_prop_simpl_new                    true
% 2.91/1.00  --sup_prop_simpl_given                  true
% 2.91/1.00  --sup_fun_splitting                     false
% 2.91/1.00  --sup_smt_interval                      50000
% 2.91/1.00  
% 2.91/1.00  ------ Superposition Simplification Setup
% 2.91/1.00  
% 2.91/1.00  --sup_indices_passive                   []
% 2.91/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.91/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_full_bw                           [BwDemod]
% 2.91/1.00  --sup_immed_triv                        [TrivRules]
% 2.91/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.91/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_immed_bw_main                     []
% 2.91/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.91/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.00  
% 2.91/1.00  ------ Combination Options
% 2.91/1.00  
% 2.91/1.00  --comb_res_mult                         3
% 2.91/1.00  --comb_sup_mult                         2
% 2.91/1.00  --comb_inst_mult                        10
% 2.91/1.00  
% 2.91/1.00  ------ Debug Options
% 2.91/1.00  
% 2.91/1.00  --dbg_backtrace                         false
% 2.91/1.00  --dbg_dump_prop_clauses                 false
% 2.91/1.00  --dbg_dump_prop_clauses_file            -
% 2.91/1.00  --dbg_out_stat                          false
% 2.91/1.00  ------ Parsing...
% 2.91/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.91/1.00  ------ Proving...
% 2.91/1.00  ------ Problem Properties 
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  clauses                                 16
% 2.91/1.00  conjectures                             3
% 2.91/1.00  EPR                                     1
% 2.91/1.00  Horn                                    14
% 2.91/1.00  unary                                   3
% 2.91/1.00  binary                                  6
% 2.91/1.00  lits                                    38
% 2.91/1.00  lits eq                                 4
% 2.91/1.00  fd_pure                                 0
% 2.91/1.00  fd_pseudo                               0
% 2.91/1.00  fd_cond                                 0
% 2.91/1.00  fd_pseudo_cond                          0
% 2.91/1.00  AC symbols                              0
% 2.91/1.00  
% 2.91/1.00  ------ Schedule dynamic 5 is on 
% 2.91/1.00  
% 2.91/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  ------ 
% 2.91/1.00  Current options:
% 2.91/1.00  ------ 
% 2.91/1.00  
% 2.91/1.00  ------ Input Options
% 2.91/1.00  
% 2.91/1.00  --out_options                           all
% 2.91/1.00  --tptp_safe_out                         true
% 2.91/1.00  --problem_path                          ""
% 2.91/1.00  --include_path                          ""
% 2.91/1.00  --clausifier                            res/vclausify_rel
% 2.91/1.00  --clausifier_options                    --mode clausify
% 2.91/1.00  --stdin                                 false
% 2.91/1.00  --stats_out                             all
% 2.91/1.00  
% 2.91/1.00  ------ General Options
% 2.91/1.00  
% 2.91/1.00  --fof                                   false
% 2.91/1.00  --time_out_real                         305.
% 2.91/1.00  --time_out_virtual                      -1.
% 2.91/1.00  --symbol_type_check                     false
% 2.91/1.00  --clausify_out                          false
% 2.91/1.00  --sig_cnt_out                           false
% 2.91/1.00  --trig_cnt_out                          false
% 2.91/1.00  --trig_cnt_out_tolerance                1.
% 2.91/1.00  --trig_cnt_out_sk_spl                   false
% 2.91/1.00  --abstr_cl_out                          false
% 2.91/1.00  
% 2.91/1.00  ------ Global Options
% 2.91/1.00  
% 2.91/1.00  --schedule                              default
% 2.91/1.00  --add_important_lit                     false
% 2.91/1.00  --prop_solver_per_cl                    1000
% 2.91/1.00  --min_unsat_core                        false
% 2.91/1.00  --soft_assumptions                      false
% 2.91/1.00  --soft_lemma_size                       3
% 2.91/1.00  --prop_impl_unit_size                   0
% 2.91/1.00  --prop_impl_unit                        []
% 2.91/1.00  --share_sel_clauses                     true
% 2.91/1.00  --reset_solvers                         false
% 2.91/1.00  --bc_imp_inh                            [conj_cone]
% 2.91/1.00  --conj_cone_tolerance                   3.
% 2.91/1.00  --extra_neg_conj                        none
% 2.91/1.00  --large_theory_mode                     true
% 2.91/1.00  --prolific_symb_bound                   200
% 2.91/1.00  --lt_threshold                          2000
% 2.91/1.00  --clause_weak_htbl                      true
% 2.91/1.00  --gc_record_bc_elim                     false
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing Options
% 2.91/1.00  
% 2.91/1.00  --preprocessing_flag                    true
% 2.91/1.00  --time_out_prep_mult                    0.1
% 2.91/1.00  --splitting_mode                        input
% 2.91/1.00  --splitting_grd                         true
% 2.91/1.00  --splitting_cvd                         false
% 2.91/1.00  --splitting_cvd_svl                     false
% 2.91/1.00  --splitting_nvd                         32
% 2.91/1.00  --sub_typing                            true
% 2.91/1.00  --prep_gs_sim                           true
% 2.91/1.00  --prep_unflatten                        true
% 2.91/1.00  --prep_res_sim                          true
% 2.91/1.00  --prep_upred                            true
% 2.91/1.00  --prep_sem_filter                       exhaustive
% 2.91/1.00  --prep_sem_filter_out                   false
% 2.91/1.00  --pred_elim                             true
% 2.91/1.00  --res_sim_input                         true
% 2.91/1.00  --eq_ax_congr_red                       true
% 2.91/1.00  --pure_diseq_elim                       true
% 2.91/1.00  --brand_transform                       false
% 2.91/1.00  --non_eq_to_eq                          false
% 2.91/1.00  --prep_def_merge                        true
% 2.91/1.00  --prep_def_merge_prop_impl              false
% 2.91/1.00  --prep_def_merge_mbd                    true
% 2.91/1.00  --prep_def_merge_tr_red                 false
% 2.91/1.00  --prep_def_merge_tr_cl                  false
% 2.91/1.00  --smt_preprocessing                     true
% 2.91/1.00  --smt_ac_axioms                         fast
% 2.91/1.00  --preprocessed_out                      false
% 2.91/1.00  --preprocessed_stats                    false
% 2.91/1.00  
% 2.91/1.00  ------ Abstraction refinement Options
% 2.91/1.00  
% 2.91/1.00  --abstr_ref                             []
% 2.91/1.00  --abstr_ref_prep                        false
% 2.91/1.00  --abstr_ref_until_sat                   false
% 2.91/1.00  --abstr_ref_sig_restrict                funpre
% 2.91/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.91/1.00  --abstr_ref_under                       []
% 2.91/1.00  
% 2.91/1.00  ------ SAT Options
% 2.91/1.00  
% 2.91/1.00  --sat_mode                              false
% 2.91/1.00  --sat_fm_restart_options                ""
% 2.91/1.00  --sat_gr_def                            false
% 2.91/1.00  --sat_epr_types                         true
% 2.91/1.00  --sat_non_cyclic_types                  false
% 2.91/1.00  --sat_finite_models                     false
% 2.91/1.00  --sat_fm_lemmas                         false
% 2.91/1.00  --sat_fm_prep                           false
% 2.91/1.00  --sat_fm_uc_incr                        true
% 2.91/1.00  --sat_out_model                         small
% 2.91/1.00  --sat_out_clauses                       false
% 2.91/1.00  
% 2.91/1.00  ------ QBF Options
% 2.91/1.00  
% 2.91/1.00  --qbf_mode                              false
% 2.91/1.00  --qbf_elim_univ                         false
% 2.91/1.00  --qbf_dom_inst                          none
% 2.91/1.00  --qbf_dom_pre_inst                      false
% 2.91/1.00  --qbf_sk_in                             false
% 2.91/1.00  --qbf_pred_elim                         true
% 2.91/1.00  --qbf_split                             512
% 2.91/1.00  
% 2.91/1.00  ------ BMC1 Options
% 2.91/1.00  
% 2.91/1.00  --bmc1_incremental                      false
% 2.91/1.00  --bmc1_axioms                           reachable_all
% 2.91/1.00  --bmc1_min_bound                        0
% 2.91/1.00  --bmc1_max_bound                        -1
% 2.91/1.00  --bmc1_max_bound_default                -1
% 2.91/1.00  --bmc1_symbol_reachability              true
% 2.91/1.00  --bmc1_property_lemmas                  false
% 2.91/1.00  --bmc1_k_induction                      false
% 2.91/1.00  --bmc1_non_equiv_states                 false
% 2.91/1.00  --bmc1_deadlock                         false
% 2.91/1.00  --bmc1_ucm                              false
% 2.91/1.00  --bmc1_add_unsat_core                   none
% 2.91/1.00  --bmc1_unsat_core_children              false
% 2.91/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.91/1.00  --bmc1_out_stat                         full
% 2.91/1.00  --bmc1_ground_init                      false
% 2.91/1.00  --bmc1_pre_inst_next_state              false
% 2.91/1.00  --bmc1_pre_inst_state                   false
% 2.91/1.00  --bmc1_pre_inst_reach_state             false
% 2.91/1.00  --bmc1_out_unsat_core                   false
% 2.91/1.00  --bmc1_aig_witness_out                  false
% 2.91/1.00  --bmc1_verbose                          false
% 2.91/1.00  --bmc1_dump_clauses_tptp                false
% 2.91/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.91/1.00  --bmc1_dump_file                        -
% 2.91/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.91/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.91/1.00  --bmc1_ucm_extend_mode                  1
% 2.91/1.00  --bmc1_ucm_init_mode                    2
% 2.91/1.00  --bmc1_ucm_cone_mode                    none
% 2.91/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.91/1.00  --bmc1_ucm_relax_model                  4
% 2.91/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.91/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.91/1.00  --bmc1_ucm_layered_model                none
% 2.91/1.00  --bmc1_ucm_max_lemma_size               10
% 2.91/1.00  
% 2.91/1.00  ------ AIG Options
% 2.91/1.00  
% 2.91/1.00  --aig_mode                              false
% 2.91/1.00  
% 2.91/1.00  ------ Instantiation Options
% 2.91/1.00  
% 2.91/1.00  --instantiation_flag                    true
% 2.91/1.00  --inst_sos_flag                         false
% 2.91/1.00  --inst_sos_phase                        true
% 2.91/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.91/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.91/1.00  --inst_lit_sel_side                     none
% 2.91/1.00  --inst_solver_per_active                1400
% 2.91/1.00  --inst_solver_calls_frac                1.
% 2.91/1.00  --inst_passive_queue_type               priority_queues
% 2.91/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.91/1.00  --inst_passive_queues_freq              [25;2]
% 2.91/1.00  --inst_dismatching                      true
% 2.91/1.00  --inst_eager_unprocessed_to_passive     true
% 2.91/1.00  --inst_prop_sim_given                   true
% 2.91/1.00  --inst_prop_sim_new                     false
% 2.91/1.00  --inst_subs_new                         false
% 2.91/1.00  --inst_eq_res_simp                      false
% 2.91/1.00  --inst_subs_given                       false
% 2.91/1.00  --inst_orphan_elimination               true
% 2.91/1.00  --inst_learning_loop_flag               true
% 2.91/1.00  --inst_learning_start                   3000
% 2.91/1.00  --inst_learning_factor                  2
% 2.91/1.00  --inst_start_prop_sim_after_learn       3
% 2.91/1.00  --inst_sel_renew                        solver
% 2.91/1.00  --inst_lit_activity_flag                true
% 2.91/1.00  --inst_restr_to_given                   false
% 2.91/1.00  --inst_activity_threshold               500
% 2.91/1.00  --inst_out_proof                        true
% 2.91/1.00  
% 2.91/1.00  ------ Resolution Options
% 2.91/1.00  
% 2.91/1.00  --resolution_flag                       false
% 2.91/1.00  --res_lit_sel                           adaptive
% 2.91/1.00  --res_lit_sel_side                      none
% 2.91/1.00  --res_ordering                          kbo
% 2.91/1.00  --res_to_prop_solver                    active
% 2.91/1.00  --res_prop_simpl_new                    false
% 2.91/1.00  --res_prop_simpl_given                  true
% 2.91/1.00  --res_passive_queue_type                priority_queues
% 2.91/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.91/1.00  --res_passive_queues_freq               [15;5]
% 2.91/1.00  --res_forward_subs                      full
% 2.91/1.00  --res_backward_subs                     full
% 2.91/1.00  --res_forward_subs_resolution           true
% 2.91/1.00  --res_backward_subs_resolution          true
% 2.91/1.00  --res_orphan_elimination                true
% 2.91/1.00  --res_time_limit                        2.
% 2.91/1.00  --res_out_proof                         true
% 2.91/1.00  
% 2.91/1.00  ------ Superposition Options
% 2.91/1.00  
% 2.91/1.00  --superposition_flag                    true
% 2.91/1.00  --sup_passive_queue_type                priority_queues
% 2.91/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.91/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.91/1.00  --demod_completeness_check              fast
% 2.91/1.00  --demod_use_ground                      true
% 2.91/1.00  --sup_to_prop_solver                    passive
% 2.91/1.00  --sup_prop_simpl_new                    true
% 2.91/1.00  --sup_prop_simpl_given                  true
% 2.91/1.00  --sup_fun_splitting                     false
% 2.91/1.00  --sup_smt_interval                      50000
% 2.91/1.00  
% 2.91/1.00  ------ Superposition Simplification Setup
% 2.91/1.00  
% 2.91/1.00  --sup_indices_passive                   []
% 2.91/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.91/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_full_bw                           [BwDemod]
% 2.91/1.00  --sup_immed_triv                        [TrivRules]
% 2.91/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.91/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_immed_bw_main                     []
% 2.91/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.91/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.00  
% 2.91/1.00  ------ Combination Options
% 2.91/1.00  
% 2.91/1.00  --comb_res_mult                         3
% 2.91/1.00  --comb_sup_mult                         2
% 2.91/1.00  --comb_inst_mult                        10
% 2.91/1.00  
% 2.91/1.00  ------ Debug Options
% 2.91/1.00  
% 2.91/1.00  --dbg_backtrace                         false
% 2.91/1.00  --dbg_dump_prop_clauses                 false
% 2.91/1.00  --dbg_dump_prop_clauses_file            -
% 2.91/1.00  --dbg_out_stat                          false
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  ------ Proving...
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  % SZS status Theorem for theBenchmark.p
% 2.91/1.00  
% 2.91/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.91/1.00  
% 2.91/1.00  fof(f9,axiom,(
% 2.91/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f22,plain,(
% 2.91/1.00    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.91/1.00    inference(ennf_transformation,[],[f9])).
% 2.91/1.00  
% 2.91/1.00  fof(f23,plain,(
% 2.91/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.91/1.00    inference(flattening,[],[f22])).
% 2.91/1.00  
% 2.91/1.00  fof(f28,plain,(
% 2.91/1.00    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f29,plain,(
% 2.91/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f28])).
% 2.91/1.00  
% 2.91/1.00  fof(f48,plain,(
% 2.91/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f29])).
% 2.91/1.00  
% 2.91/1.00  fof(f58,plain,(
% 2.91/1.00    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.91/1.00    inference(equality_resolution,[],[f48])).
% 2.91/1.00  
% 2.91/1.00  fof(f10,conjecture,(
% 2.91/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f11,negated_conjecture,(
% 2.91/1.00    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 2.91/1.00    inference(negated_conjecture,[],[f10])).
% 2.91/1.00  
% 2.91/1.00  fof(f24,plain,(
% 2.91/1.00    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 2.91/1.00    inference(ennf_transformation,[],[f11])).
% 2.91/1.00  
% 2.91/1.00  fof(f25,plain,(
% 2.91/1.00    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 2.91/1.00    inference(flattening,[],[f24])).
% 2.91/1.00  
% 2.91/1.00  fof(f32,plain,(
% 2.91/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK4),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f31,plain,(
% 2.91/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK3,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) & v1_funct_2(X3,X1,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))) )),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f30,plain,(
% 2.91/1.00    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK2,X2,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_2(X3,sK2,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f33,plain,(
% 2.91/1.00    ((~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 2.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f32,f31,f30])).
% 2.91/1.00  
% 2.91/1.00  fof(f52,plain,(
% 2.91/1.00    v1_funct_1(sK4)),
% 2.91/1.00    inference(cnf_transformation,[],[f33])).
% 2.91/1.00  
% 2.91/1.00  fof(f54,plain,(
% 2.91/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.91/1.00    inference(cnf_transformation,[],[f33])).
% 2.91/1.00  
% 2.91/1.00  fof(f4,axiom,(
% 2.91/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f16,plain,(
% 2.91/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.91/1.00    inference(ennf_transformation,[],[f4])).
% 2.91/1.00  
% 2.91/1.00  fof(f39,plain,(
% 2.91/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.91/1.00    inference(cnf_transformation,[],[f16])).
% 2.91/1.00  
% 2.91/1.00  fof(f1,axiom,(
% 2.91/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f26,plain,(
% 2.91/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.91/1.00    inference(nnf_transformation,[],[f1])).
% 2.91/1.00  
% 2.91/1.00  fof(f35,plain,(
% 2.91/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f26])).
% 2.91/1.00  
% 2.91/1.00  fof(f5,axiom,(
% 2.91/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f12,plain,(
% 2.91/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.91/1.00    inference(pure_predicate_removal,[],[f5])).
% 2.91/1.00  
% 2.91/1.00  fof(f17,plain,(
% 2.91/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.91/1.00    inference(ennf_transformation,[],[f12])).
% 2.91/1.00  
% 2.91/1.00  fof(f40,plain,(
% 2.91/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.91/1.00    inference(cnf_transformation,[],[f17])).
% 2.91/1.00  
% 2.91/1.00  fof(f3,axiom,(
% 2.91/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f15,plain,(
% 2.91/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.91/1.00    inference(ennf_transformation,[],[f3])).
% 2.91/1.00  
% 2.91/1.00  fof(f27,plain,(
% 2.91/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.91/1.00    inference(nnf_transformation,[],[f15])).
% 2.91/1.00  
% 2.91/1.00  fof(f37,plain,(
% 2.91/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f27])).
% 2.91/1.00  
% 2.91/1.00  fof(f2,axiom,(
% 2.91/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f13,plain,(
% 2.91/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.91/1.00    inference(ennf_transformation,[],[f2])).
% 2.91/1.00  
% 2.91/1.00  fof(f14,plain,(
% 2.91/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.91/1.00    inference(flattening,[],[f13])).
% 2.91/1.00  
% 2.91/1.00  fof(f36,plain,(
% 2.91/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f14])).
% 2.91/1.00  
% 2.91/1.00  fof(f8,axiom,(
% 2.91/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f20,plain,(
% 2.91/1.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.91/1.00    inference(ennf_transformation,[],[f8])).
% 2.91/1.00  
% 2.91/1.00  fof(f21,plain,(
% 2.91/1.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.91/1.00    inference(flattening,[],[f20])).
% 2.91/1.00  
% 2.91/1.00  fof(f43,plain,(
% 2.91/1.00    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f21])).
% 2.91/1.00  
% 2.91/1.00  fof(f50,plain,(
% 2.91/1.00    ~v1_xboole_0(sK2)),
% 2.91/1.00    inference(cnf_transformation,[],[f33])).
% 2.91/1.00  
% 2.91/1.00  fof(f53,plain,(
% 2.91/1.00    v1_funct_2(sK4,sK2,sK3)),
% 2.91/1.00    inference(cnf_transformation,[],[f33])).
% 2.91/1.00  
% 2.91/1.00  fof(f7,axiom,(
% 2.91/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f19,plain,(
% 2.91/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.91/1.00    inference(ennf_transformation,[],[f7])).
% 2.91/1.00  
% 2.91/1.00  fof(f42,plain,(
% 2.91/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.91/1.00    inference(cnf_transformation,[],[f19])).
% 2.91/1.00  
% 2.91/1.00  fof(f55,plain,(
% 2.91/1.00    ( ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f33])).
% 2.91/1.00  
% 2.91/1.00  fof(f49,plain,(
% 2.91/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f29])).
% 2.91/1.00  
% 2.91/1.00  fof(f57,plain,(
% 2.91/1.00    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.91/1.00    inference(equality_resolution,[],[f49])).
% 2.91/1.00  
% 2.91/1.00  fof(f6,axiom,(
% 2.91/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f18,plain,(
% 2.91/1.00    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.91/1.00    inference(ennf_transformation,[],[f6])).
% 2.91/1.00  
% 2.91/1.00  fof(f41,plain,(
% 2.91/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.91/1.00    inference(cnf_transformation,[],[f18])).
% 2.91/1.00  
% 2.91/1.00  fof(f34,plain,(
% 2.91/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.91/1.00    inference(cnf_transformation,[],[f26])).
% 2.91/1.00  
% 2.91/1.00  fof(f56,plain,(
% 2.91/1.00    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)),
% 2.91/1.00    inference(cnf_transformation,[],[f33])).
% 2.91/1.00  
% 2.91/1.00  fof(f47,plain,(
% 2.91/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f29])).
% 2.91/1.00  
% 2.91/1.00  fof(f59,plain,(
% 2.91/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.91/1.00    inference(equality_resolution,[],[f47])).
% 2.91/1.00  
% 2.91/1.00  cnf(c_11,plain,
% 2.91/1.00      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 2.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.91/1.00      | ~ v1_funct_1(X0)
% 2.91/1.00      | ~ v1_relat_1(X0) ),
% 2.91/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_20,negated_conjecture,
% 2.91/1.00      ( v1_funct_1(sK4) ),
% 2.91/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_553,plain,
% 2.91/1.00      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 2.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.91/1.00      | ~ v1_relat_1(X0)
% 2.91/1.00      | sK4 != X0 ),
% 2.91/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_554,plain,
% 2.91/1.00      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 2.91/1.00      | ~ v1_relat_1(sK4) ),
% 2.91/1.00      inference(unflattening,[status(thm)],[c_553]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1861,plain,
% 2.91/1.00      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 2.91/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_18,negated_conjecture,
% 2.91/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.91/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_27,plain,
% 2.91/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_555,plain,
% 2.91/1.00      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 2.91/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_5,plain,
% 2.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.91/1.00      | v1_relat_1(X0) ),
% 2.91/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1992,plain,
% 2.91/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.91/1.00      | v1_relat_1(sK4) ),
% 2.91/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1993,plain,
% 2.91/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.91/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1992]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2194,plain,
% 2.91/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 2.91/1.00      | r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_1861,c_27,c_555,c_1993]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2195,plain,
% 2.91/1.00      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 2.91/1.00      inference(renaming,[status(thm)],[c_2194]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1870,plain,
% 2.91/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_0,plain,
% 2.91/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.91/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_173,plain,
% 2.91/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.91/1.00      inference(prop_impl,[status(thm)],[c_0]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_6,plain,
% 2.91/1.00      ( v4_relat_1(X0,X1)
% 2.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.91/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4,plain,
% 2.91/1.00      ( ~ v4_relat_1(X0,X1)
% 2.91/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 2.91/1.00      | ~ v1_relat_1(X0) ),
% 2.91/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_288,plain,
% 2.91/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 2.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.91/1.00      | ~ v1_relat_1(X0) ),
% 2.91/1.00      inference(resolution,[status(thm)],[c_6,c_4]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_292,plain,
% 2.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.91/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_288,c_6,c_5,c_4]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_293,plain,
% 2.91/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 2.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.91/1.00      inference(renaming,[status(thm)],[c_292]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_310,plain,
% 2.91/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.91/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.91/1.00      | X3 != X1
% 2.91/1.00      | k1_relat_1(X2) != X0 ),
% 2.91/1.00      inference(resolution_lifted,[status(thm)],[c_173,c_293]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_311,plain,
% 2.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.91/1.00      | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1)) ),
% 2.91/1.00      inference(unflattening,[status(thm)],[c_310]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1868,plain,
% 2.91/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.91/1.00      | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2656,plain,
% 2.91/1.00      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_1870,c_1868]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2,plain,
% 2.91/1.00      ( ~ r2_hidden(X0,X1)
% 2.91/1.00      | m1_subset_1(X0,X2)
% 2.91/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.91/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1875,plain,
% 2.91/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.91/1.00      | m1_subset_1(X0,X2) = iProver_top
% 2.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2717,plain,
% 2.91/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.91/1.00      | m1_subset_1(X0,sK2) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_2656,c_1875]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2725,plain,
% 2.91/1.00      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),sK2) = iProver_top
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_2195,c_2717]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_9,plain,
% 2.91/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.91/1.00      | ~ m1_subset_1(X3,X1)
% 2.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.91/1.00      | v1_xboole_0(X1)
% 2.91/1.00      | ~ v1_funct_1(X0)
% 2.91/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.91/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_22,negated_conjecture,
% 2.91/1.00      ( ~ v1_xboole_0(sK2) ),
% 2.91/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_370,plain,
% 2.91/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.91/1.00      | ~ m1_subset_1(X3,X1)
% 2.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.91/1.00      | ~ v1_funct_1(X0)
% 2.91/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 2.91/1.00      | sK2 != X1 ),
% 2.91/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_371,plain,
% 2.91/1.00      ( ~ v1_funct_2(X0,sK2,X1)
% 2.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 2.91/1.00      | ~ m1_subset_1(X2,sK2)
% 2.91/1.00      | ~ v1_funct_1(X0)
% 2.91/1.00      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.91/1.00      inference(unflattening,[status(thm)],[c_370]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_487,plain,
% 2.91/1.00      ( ~ v1_funct_2(X0,sK2,X1)
% 2.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 2.91/1.00      | ~ m1_subset_1(X2,sK2)
% 2.91/1.00      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
% 2.91/1.00      | sK4 != X0 ),
% 2.91/1.00      inference(resolution_lifted,[status(thm)],[c_371,c_20]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_488,plain,
% 2.91/1.00      ( ~ v1_funct_2(sK4,sK2,X0)
% 2.91/1.00      | ~ m1_subset_1(X1,sK2)
% 2.91/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.91/1.00      | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
% 2.91/1.00      inference(unflattening,[status(thm)],[c_487]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1865,plain,
% 2.91/1.00      ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 2.91/1.00      | v1_funct_2(sK4,sK2,X0) != iProver_top
% 2.91/1.00      | m1_subset_1(X1,sK2) != iProver_top
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2509,plain,
% 2.91/1.00      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 2.91/1.00      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 2.91/1.00      | m1_subset_1(X0,sK2) != iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_1870,c_1865]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_19,negated_conjecture,
% 2.91/1.00      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.91/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_681,plain,
% 2.91/1.00      ( ~ m1_subset_1(X0,sK2)
% 2.91/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 2.91/1.00      | k3_funct_2(sK2,X1,sK4,X0) = k1_funct_1(sK4,X0)
% 2.91/1.00      | sK4 != sK4
% 2.91/1.00      | sK3 != X1
% 2.91/1.00      | sK2 != sK2 ),
% 2.91/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_488]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_682,plain,
% 2.91/1.00      ( ~ m1_subset_1(X0,sK2)
% 2.91/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.91/1.00      | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0) ),
% 2.91/1.00      inference(unflattening,[status(thm)],[c_681]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_686,plain,
% 2.91/1.00      ( ~ m1_subset_1(X0,sK2)
% 2.91/1.00      | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0) ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_682,c_18]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_688,plain,
% 2.91/1.00      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 2.91/1.00      | m1_subset_1(X0,sK2) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2512,plain,
% 2.91/1.00      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 2.91/1.00      | m1_subset_1(X0,sK2) != iProver_top ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_2509,c_688]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2833,plain,
% 2.91/1.00      ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),X0,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4))
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_2725,c_2512]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_8,plain,
% 2.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.91/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.91/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1872,plain,
% 2.91/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.91/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2896,plain,
% 2.91/1.00      ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),X0,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4))
% 2.91/1.00      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_2833,c_1872]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_17,negated_conjecture,
% 2.91/1.00      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
% 2.91/1.00      | ~ m1_subset_1(X0,sK2) ),
% 2.91/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1871,plain,
% 2.91/1.00      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top
% 2.91/1.00      | m1_subset_1(X0,sK2) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2946,plain,
% 2.91/1.00      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 2.91/1.00      | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),sK1) = iProver_top
% 2.91/1.00      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),sK2) != iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_2896,c_1871]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2053,plain,
% 2.91/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 2.91/1.00      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
% 2.91/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2069,plain,
% 2.91/1.00      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_2053]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2951,plain,
% 2.91/1.00      ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),sK1) = iProver_top
% 2.91/1.00      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_2946,c_2069,c_2725]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2952,plain,
% 2.91/1.00      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 2.91/1.00      | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),sK1) = iProver_top ),
% 2.91/1.00      inference(renaming,[status(thm)],[c_2951]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_10,plain,
% 2.91/1.00      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 2.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.91/1.00      | ~ v1_funct_1(X0)
% 2.91/1.00      | ~ v1_relat_1(X0) ),
% 2.91/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_568,plain,
% 2.91/1.00      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 2.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.91/1.00      | ~ v1_relat_1(X0)
% 2.91/1.00      | sK4 != X0 ),
% 2.91/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_569,plain,
% 2.91/1.00      ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 2.91/1.00      | ~ v1_relat_1(sK4) ),
% 2.91/1.00      inference(unflattening,[status(thm)],[c_568]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1860,plain,
% 2.91/1.00      ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 2.91/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_569]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_570,plain,
% 2.91/1.00      ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 2.91/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_569]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2096,plain,
% 2.91/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 2.91/1.00      | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_1860,c_27,c_570,c_1993]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2097,plain,
% 2.91/1.00      ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 2.91/1.00      inference(renaming,[status(thm)],[c_2096]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2959,plain,
% 2.91/1.00      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_2952,c_2097]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3030,plain,
% 2.91/1.00      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4) ),
% 2.91/1.00      inference(forward_subsumption_resolution,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_2959,c_1872]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_7,plain,
% 2.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.91/1.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.91/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1873,plain,
% 2.91/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.91/1.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3031,plain,
% 2.91/1.00      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_3030,c_1873]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2266,plain,
% 2.91/1.00      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_1870,c_1872]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1,plain,
% 2.91/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.91/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_171,plain,
% 2.91/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.91/1.00      inference(prop_impl,[status(thm)],[c_1]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_16,negated_conjecture,
% 2.91/1.00      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
% 2.91/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_322,plain,
% 2.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.91/1.00      | k2_relset_1(sK2,sK3,sK4) != X0
% 2.91/1.00      | sK1 != X1 ),
% 2.91/1.00      inference(resolution_lifted,[status(thm)],[c_171,c_16]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_323,plain,
% 2.91/1.00      ( ~ m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) ),
% 2.91/1.00      inference(unflattening,[status(thm)],[c_322]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1867,plain,
% 2.91/1.00      ( m1_subset_1(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK1)) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2401,plain,
% 2.91/1.00      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) != iProver_top ),
% 2.91/1.00      inference(demodulation,[status(thm)],[c_2266,c_1867]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3096,plain,
% 2.91/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_3031,c_2401]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3101,plain,
% 2.91/1.00      ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),sK1,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_2833,c_3096]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3275,plain,
% 2.91/1.00      ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)),sK1) = iProver_top
% 2.91/1.00      | m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2) != iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_3101,c_1871]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_12,plain,
% 2.91/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.91/1.00      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 2.91/1.00      | ~ v1_funct_1(X0)
% 2.91/1.00      | ~ v1_relat_1(X0) ),
% 2.91/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_538,plain,
% 2.91/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.91/1.00      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 2.91/1.00      | ~ v1_relat_1(X0)
% 2.91/1.00      | sK4 != X0 ),
% 2.91/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_539,plain,
% 2.91/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 2.91/1.00      | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 2.91/1.00      | ~ v1_relat_1(sK4) ),
% 2.91/1.00      inference(unflattening,[status(thm)],[c_538]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1862,plain,
% 2.91/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 2.91/1.00      | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
% 2.91/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_540,plain,
% 2.91/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 2.91/1.00      | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
% 2.91/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2025,plain,
% 2.91/1.00      ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top
% 2.91/1.00      | v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_1862,c_27,c_540,c_1993]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_2026,plain,
% 2.91/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0) = iProver_top
% 2.91/1.00      | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0) != iProver_top ),
% 2.91/1.00      inference(renaming,[status(thm)],[c_2025]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3397,plain,
% 2.91/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),sK1) = iProver_top
% 2.91/1.00      | m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2) != iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_3275,c_2026]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3396,plain,
% 2.91/1.00      ( m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2) != iProver_top
% 2.91/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_3275,c_2097]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3409,plain,
% 2.91/1.00      ( m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2) != iProver_top ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_3397,c_2401,c_3031,c_3396]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3414,plain,
% 2.91/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_2725,c_3409]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(contradiction,plain,
% 2.91/1.00      ( $false ),
% 2.91/1.00      inference(minisat,[status(thm)],[c_3414,c_3031,c_2401]) ).
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.91/1.00  
% 2.91/1.00  ------                               Statistics
% 2.91/1.00  
% 2.91/1.00  ------ General
% 2.91/1.00  
% 2.91/1.00  abstr_ref_over_cycles:                  0
% 2.91/1.00  abstr_ref_under_cycles:                 0
% 2.91/1.00  gc_basic_clause_elim:                   0
% 2.91/1.00  forced_gc_time:                         0
% 2.91/1.00  parsing_time:                           0.01
% 2.91/1.00  unif_index_cands_time:                  0.
% 2.91/1.00  unif_index_add_time:                    0.
% 2.91/1.00  orderings_time:                         0.
% 2.91/1.00  out_proof_time:                         0.009
% 2.91/1.00  total_time:                             0.16
% 2.91/1.00  num_of_symbols:                         51
% 2.91/1.00  num_of_terms:                           2344
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing
% 2.91/1.00  
% 2.91/1.00  num_of_splits:                          0
% 2.91/1.00  num_of_split_atoms:                     0
% 2.91/1.00  num_of_reused_defs:                     0
% 2.91/1.00  num_eq_ax_congr_red:                    15
% 2.91/1.00  num_of_sem_filtered_clauses:            1
% 2.91/1.00  num_of_subtypes:                        1
% 2.91/1.00  monotx_restored_types:                  0
% 2.91/1.00  sat_num_of_epr_types:                   0
% 2.91/1.00  sat_num_of_non_cyclic_types:            0
% 2.91/1.00  sat_guarded_non_collapsed_types:        0
% 2.91/1.00  num_pure_diseq_elim:                    0
% 2.91/1.00  simp_replaced_by:                       0
% 2.91/1.00  res_preprocessed:                       96
% 2.91/1.00  prep_upred:                             0
% 2.91/1.00  prep_unflattend:                        57
% 2.91/1.00  smt_new_axioms:                         0
% 2.91/1.00  pred_elim_cands:                        4
% 2.91/1.00  pred_elim:                              4
% 2.91/1.00  pred_elim_cl:                           5
% 2.91/1.00  pred_elim_cycles:                       11
% 2.91/1.00  merged_defs:                            2
% 2.91/1.00  merged_defs_ncl:                        0
% 2.91/1.00  bin_hyper_res:                          2
% 2.91/1.00  prep_cycles:                            4
% 2.91/1.00  pred_elim_time:                         0.043
% 2.91/1.00  splitting_time:                         0.
% 2.91/1.00  sem_filter_time:                        0.
% 2.91/1.00  monotx_time:                            0.
% 2.91/1.00  subtype_inf_time:                       0.
% 2.91/1.00  
% 2.91/1.00  ------ Problem properties
% 2.91/1.00  
% 2.91/1.00  clauses:                                16
% 2.91/1.00  conjectures:                            3
% 2.91/1.00  epr:                                    1
% 2.91/1.00  horn:                                   14
% 2.91/1.00  ground:                                 3
% 2.91/1.00  unary:                                  3
% 2.91/1.00  binary:                                 6
% 2.91/1.00  lits:                                   38
% 2.91/1.00  lits_eq:                                4
% 2.91/1.00  fd_pure:                                0
% 2.91/1.00  fd_pseudo:                              0
% 2.91/1.00  fd_cond:                                0
% 2.91/1.00  fd_pseudo_cond:                         0
% 2.91/1.00  ac_symbols:                             0
% 2.91/1.00  
% 2.91/1.00  ------ Propositional Solver
% 2.91/1.00  
% 2.91/1.00  prop_solver_calls:                      27
% 2.91/1.00  prop_fast_solver_calls:                 836
% 2.91/1.00  smt_solver_calls:                       0
% 2.91/1.00  smt_fast_solver_calls:                  0
% 2.91/1.00  prop_num_of_clauses:                    922
% 2.91/1.00  prop_preprocess_simplified:             3730
% 2.91/1.00  prop_fo_subsumed:                       16
% 2.91/1.00  prop_solver_time:                       0.
% 2.91/1.00  smt_solver_time:                        0.
% 2.91/1.00  smt_fast_solver_time:                   0.
% 2.91/1.00  prop_fast_solver_time:                  0.
% 2.91/1.00  prop_unsat_core_time:                   0.
% 2.91/1.00  
% 2.91/1.00  ------ QBF
% 2.91/1.00  
% 2.91/1.00  qbf_q_res:                              0
% 2.91/1.00  qbf_num_tautologies:                    0
% 2.91/1.00  qbf_prep_cycles:                        0
% 2.91/1.00  
% 2.91/1.00  ------ BMC1
% 2.91/1.00  
% 2.91/1.00  bmc1_current_bound:                     -1
% 2.91/1.00  bmc1_last_solved_bound:                 -1
% 2.91/1.00  bmc1_unsat_core_size:                   -1
% 2.91/1.00  bmc1_unsat_core_parents_size:           -1
% 2.91/1.00  bmc1_merge_next_fun:                    0
% 2.91/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.91/1.00  
% 2.91/1.00  ------ Instantiation
% 2.91/1.00  
% 2.91/1.00  inst_num_of_clauses:                    237
% 2.91/1.00  inst_num_in_passive:                    46
% 2.91/1.00  inst_num_in_active:                     181
% 2.91/1.00  inst_num_in_unprocessed:                10
% 2.91/1.00  inst_num_of_loops:                      210
% 2.91/1.00  inst_num_of_learning_restarts:          0
% 2.91/1.00  inst_num_moves_active_passive:          24
% 2.91/1.00  inst_lit_activity:                      0
% 2.91/1.00  inst_lit_activity_moves:                0
% 2.91/1.00  inst_num_tautologies:                   0
% 2.91/1.00  inst_num_prop_implied:                  0
% 2.91/1.00  inst_num_existing_simplified:           0
% 2.91/1.00  inst_num_eq_res_simplified:             0
% 2.91/1.00  inst_num_child_elim:                    0
% 2.91/1.00  inst_num_of_dismatching_blockings:      45
% 2.91/1.00  inst_num_of_non_proper_insts:           240
% 2.91/1.00  inst_num_of_duplicates:                 0
% 2.91/1.00  inst_inst_num_from_inst_to_res:         0
% 2.91/1.00  inst_dismatching_checking_time:         0.
% 2.91/1.00  
% 2.91/1.00  ------ Resolution
% 2.91/1.00  
% 2.91/1.00  res_num_of_clauses:                     0
% 2.91/1.00  res_num_in_passive:                     0
% 2.91/1.00  res_num_in_active:                      0
% 2.91/1.00  res_num_of_loops:                       100
% 2.91/1.00  res_forward_subset_subsumed:            39
% 2.91/1.00  res_backward_subset_subsumed:           0
% 2.91/1.00  res_forward_subsumed:                   0
% 2.91/1.00  res_backward_subsumed:                  0
% 2.91/1.00  res_forward_subsumption_resolution:     4
% 2.91/1.00  res_backward_subsumption_resolution:    0
% 2.91/1.00  res_clause_to_clause_subsumption:       101
% 2.91/1.00  res_orphan_elimination:                 0
% 2.91/1.00  res_tautology_del:                      64
% 2.91/1.00  res_num_eq_res_simplified:              0
% 2.91/1.00  res_num_sel_changes:                    0
% 2.91/1.00  res_moves_from_active_to_pass:          0
% 2.91/1.00  
% 2.91/1.00  ------ Superposition
% 2.91/1.00  
% 2.91/1.00  sup_time_total:                         0.
% 2.91/1.00  sup_time_generating:                    0.
% 2.91/1.00  sup_time_sim_full:                      0.
% 2.91/1.00  sup_time_sim_immed:                     0.
% 2.91/1.00  
% 2.91/1.00  sup_num_of_clauses:                     52
% 2.91/1.00  sup_num_in_active:                      39
% 2.91/1.00  sup_num_in_passive:                     13
% 2.91/1.00  sup_num_of_loops:                       41
% 2.91/1.00  sup_fw_superposition:                   18
% 2.91/1.00  sup_bw_superposition:                   24
% 2.91/1.00  sup_immediate_simplified:               3
% 2.91/1.00  sup_given_eliminated:                   0
% 2.91/1.00  comparisons_done:                       0
% 2.91/1.00  comparisons_avoided:                    3
% 2.91/1.00  
% 2.91/1.00  ------ Simplifications
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  sim_fw_subset_subsumed:                 3
% 2.91/1.00  sim_bw_subset_subsumed:                 2
% 2.91/1.00  sim_fw_subsumed:                        0
% 2.91/1.00  sim_bw_subsumed:                        0
% 2.91/1.00  sim_fw_subsumption_res:                 1
% 2.91/1.00  sim_bw_subsumption_res:                 0
% 2.91/1.00  sim_tautology_del:                      0
% 2.91/1.00  sim_eq_tautology_del:                   0
% 2.91/1.00  sim_eq_res_simp:                        0
% 2.91/1.00  sim_fw_demodulated:                     0
% 2.91/1.00  sim_bw_demodulated:                     2
% 2.91/1.00  sim_light_normalised:                   0
% 2.91/1.00  sim_joinable_taut:                      0
% 2.91/1.00  sim_joinable_simp:                      0
% 2.91/1.00  sim_ac_normalised:                      0
% 2.91/1.00  sim_smt_subsumption:                    0
% 2.91/1.00  
%------------------------------------------------------------------------------
