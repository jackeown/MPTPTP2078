%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:13 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 990 expanded)
%              Number of clauses        :   84 ( 303 expanded)
%              Number of leaves         :   15 ( 274 expanded)
%              Depth                    :   20
%              Number of atoms          :  490 (6017 expanded)
%              Number of equality atoms :  155 ( 545 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f24])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f30])).

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

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f26])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f34,f33,f32])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f58,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f35])).

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

cnf(c_556,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_557,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_696,plain,
    ( m1_subset_1(X0,X1)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X2)))
    | ~ v1_relat_1(sK4)
    | sK0(k1_relat_1(sK4),X2,sK4) != X0
    | k1_relat_1(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_557])).

cnf(c_697,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_696])).

cnf(c_1829,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_698,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2058,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2059,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2058])).

cnf(c_3786,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1829,c_32,c_698,c_2059])).

cnf(c_3787,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3786])).

cnf(c_1835,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1836,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2875,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1835,c_1836])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1843,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2270,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1835,c_1843])).

cnf(c_2897,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2875,c_2270])).

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

cnf(c_342,plain,
    ( sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_26])).

cnf(c_2997,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2897,c_31,c_342])).

cnf(c_3792,plain,
    ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3787,c_2997])).

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

cnf(c_371,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_372,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_490,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_372,c_25])).

cnf(c_491,plain,
    ( ~ v1_funct_2(sK4,sK2,X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_1832,plain,
    ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | v1_funct_2(sK4,sK2,X0) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_2098,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1835,c_1832])).

cnf(c_2405,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2098,c_31])).

cnf(c_3798,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3792,c_2405])).

cnf(c_5,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_303,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_304,plain,
    ( ~ v5_relat_1(X0,sK1)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X3)
    | X3 != X0
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X3)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_304])).

cnf(c_323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_323,c_4])).

cnf(c_1833,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_333])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1842,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2266,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1835,c_1842])).

cnf(c_4100,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK4)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1833,c_2266])).

cnf(c_4106,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4100])).

cnf(c_4224,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4)) ),
    inference(superposition,[status(thm)],[c_3798,c_4106])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
    | ~ m1_subset_1(X0,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_684,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,sK2)
    | k3_funct_2(sK2,sK3,sK4,X2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_685,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_1830,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_685])).

cnf(c_4387,plain,
    ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | m1_subset_1(k1_funct_1(sK4,sK0(sK2,sK1,sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4224,c_1830])).

cnf(c_15,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_571,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_572,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_726,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_572])).

cnf(c_727,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_1360,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | ~ v1_relat_1(sK4)
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_727])).

cnf(c_1826,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1360])).

cnf(c_1404,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1360])).

cnf(c_2486,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1826,c_32,c_1404,c_2059])).

cnf(c_3005,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2997,c_2486])).

cnf(c_4225,plain,
    ( sP2_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_3005,c_4106])).

cnf(c_17,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_541,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_542,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_744,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)) != k3_funct_2(sK2,sK3,sK4,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_542])).

cnf(c_745,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),sK1)
    | ~ m1_subset_1(X0,sK2)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_1358,plain,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_745])).

cnf(c_1825,plain,
    ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1358])).

cnf(c_3009,plain,
    ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2997,c_1825])).

cnf(c_4386,plain,
    ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4224,c_3009])).

cnf(c_4451,plain,
    ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4387,c_4225,c_4386])).

cnf(c_4456,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3792,c_4451])).

cnf(c_4511,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4456,c_4106])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:12:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.10/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.03  
% 2.10/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.10/1.03  
% 2.10/1.03  ------  iProver source info
% 2.10/1.03  
% 2.10/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.10/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.10/1.03  git: non_committed_changes: false
% 2.10/1.03  git: last_make_outside_of_git: false
% 2.10/1.03  
% 2.10/1.03  ------ 
% 2.10/1.03  
% 2.10/1.03  ------ Input Options
% 2.10/1.03  
% 2.10/1.03  --out_options                           all
% 2.10/1.03  --tptp_safe_out                         true
% 2.10/1.03  --problem_path                          ""
% 2.10/1.03  --include_path                          ""
% 2.10/1.03  --clausifier                            res/vclausify_rel
% 2.10/1.03  --clausifier_options                    --mode clausify
% 2.10/1.03  --stdin                                 false
% 2.10/1.03  --stats_out                             all
% 2.10/1.03  
% 2.10/1.03  ------ General Options
% 2.10/1.03  
% 2.10/1.03  --fof                                   false
% 2.10/1.03  --time_out_real                         305.
% 2.10/1.03  --time_out_virtual                      -1.
% 2.10/1.03  --symbol_type_check                     false
% 2.10/1.03  --clausify_out                          false
% 2.10/1.03  --sig_cnt_out                           false
% 2.10/1.03  --trig_cnt_out                          false
% 2.10/1.03  --trig_cnt_out_tolerance                1.
% 2.10/1.03  --trig_cnt_out_sk_spl                   false
% 2.10/1.03  --abstr_cl_out                          false
% 2.10/1.03  
% 2.10/1.03  ------ Global Options
% 2.10/1.03  
% 2.10/1.03  --schedule                              default
% 2.10/1.03  --add_important_lit                     false
% 2.10/1.03  --prop_solver_per_cl                    1000
% 2.10/1.03  --min_unsat_core                        false
% 2.10/1.03  --soft_assumptions                      false
% 2.10/1.03  --soft_lemma_size                       3
% 2.10/1.03  --prop_impl_unit_size                   0
% 2.10/1.03  --prop_impl_unit                        []
% 2.10/1.03  --share_sel_clauses                     true
% 2.10/1.03  --reset_solvers                         false
% 2.10/1.03  --bc_imp_inh                            [conj_cone]
% 2.10/1.03  --conj_cone_tolerance                   3.
% 2.10/1.03  --extra_neg_conj                        none
% 2.10/1.03  --large_theory_mode                     true
% 2.10/1.03  --prolific_symb_bound                   200
% 2.10/1.03  --lt_threshold                          2000
% 2.10/1.03  --clause_weak_htbl                      true
% 2.10/1.03  --gc_record_bc_elim                     false
% 2.10/1.03  
% 2.10/1.03  ------ Preprocessing Options
% 2.10/1.03  
% 2.10/1.03  --preprocessing_flag                    true
% 2.10/1.03  --time_out_prep_mult                    0.1
% 2.10/1.03  --splitting_mode                        input
% 2.10/1.03  --splitting_grd                         true
% 2.10/1.03  --splitting_cvd                         false
% 2.10/1.03  --splitting_cvd_svl                     false
% 2.10/1.03  --splitting_nvd                         32
% 2.10/1.03  --sub_typing                            true
% 2.10/1.03  --prep_gs_sim                           true
% 2.10/1.03  --prep_unflatten                        true
% 2.10/1.03  --prep_res_sim                          true
% 2.10/1.03  --prep_upred                            true
% 2.10/1.03  --prep_sem_filter                       exhaustive
% 2.10/1.03  --prep_sem_filter_out                   false
% 2.10/1.03  --pred_elim                             true
% 2.10/1.03  --res_sim_input                         true
% 2.10/1.03  --eq_ax_congr_red                       true
% 2.10/1.03  --pure_diseq_elim                       true
% 2.10/1.03  --brand_transform                       false
% 2.10/1.03  --non_eq_to_eq                          false
% 2.10/1.03  --prep_def_merge                        true
% 2.10/1.03  --prep_def_merge_prop_impl              false
% 2.10/1.03  --prep_def_merge_mbd                    true
% 2.10/1.03  --prep_def_merge_tr_red                 false
% 2.10/1.03  --prep_def_merge_tr_cl                  false
% 2.10/1.03  --smt_preprocessing                     true
% 2.10/1.03  --smt_ac_axioms                         fast
% 2.10/1.03  --preprocessed_out                      false
% 2.10/1.03  --preprocessed_stats                    false
% 2.10/1.03  
% 2.10/1.03  ------ Abstraction refinement Options
% 2.10/1.03  
% 2.10/1.03  --abstr_ref                             []
% 2.10/1.03  --abstr_ref_prep                        false
% 2.10/1.03  --abstr_ref_until_sat                   false
% 2.10/1.03  --abstr_ref_sig_restrict                funpre
% 2.10/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/1.03  --abstr_ref_under                       []
% 2.10/1.03  
% 2.10/1.03  ------ SAT Options
% 2.10/1.03  
% 2.10/1.03  --sat_mode                              false
% 2.10/1.03  --sat_fm_restart_options                ""
% 2.10/1.03  --sat_gr_def                            false
% 2.10/1.03  --sat_epr_types                         true
% 2.10/1.03  --sat_non_cyclic_types                  false
% 2.10/1.03  --sat_finite_models                     false
% 2.10/1.03  --sat_fm_lemmas                         false
% 2.10/1.03  --sat_fm_prep                           false
% 2.10/1.03  --sat_fm_uc_incr                        true
% 2.10/1.03  --sat_out_model                         small
% 2.10/1.03  --sat_out_clauses                       false
% 2.10/1.03  
% 2.10/1.03  ------ QBF Options
% 2.10/1.03  
% 2.10/1.03  --qbf_mode                              false
% 2.10/1.03  --qbf_elim_univ                         false
% 2.10/1.03  --qbf_dom_inst                          none
% 2.10/1.03  --qbf_dom_pre_inst                      false
% 2.10/1.03  --qbf_sk_in                             false
% 2.10/1.03  --qbf_pred_elim                         true
% 2.10/1.03  --qbf_split                             512
% 2.10/1.03  
% 2.10/1.03  ------ BMC1 Options
% 2.10/1.03  
% 2.10/1.03  --bmc1_incremental                      false
% 2.10/1.03  --bmc1_axioms                           reachable_all
% 2.10/1.03  --bmc1_min_bound                        0
% 2.10/1.03  --bmc1_max_bound                        -1
% 2.10/1.03  --bmc1_max_bound_default                -1
% 2.10/1.03  --bmc1_symbol_reachability              true
% 2.10/1.03  --bmc1_property_lemmas                  false
% 2.10/1.03  --bmc1_k_induction                      false
% 2.10/1.03  --bmc1_non_equiv_states                 false
% 2.10/1.03  --bmc1_deadlock                         false
% 2.10/1.03  --bmc1_ucm                              false
% 2.10/1.03  --bmc1_add_unsat_core                   none
% 2.10/1.03  --bmc1_unsat_core_children              false
% 2.10/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/1.03  --bmc1_out_stat                         full
% 2.10/1.03  --bmc1_ground_init                      false
% 2.10/1.03  --bmc1_pre_inst_next_state              false
% 2.10/1.03  --bmc1_pre_inst_state                   false
% 2.10/1.03  --bmc1_pre_inst_reach_state             false
% 2.10/1.03  --bmc1_out_unsat_core                   false
% 2.10/1.03  --bmc1_aig_witness_out                  false
% 2.10/1.03  --bmc1_verbose                          false
% 2.10/1.03  --bmc1_dump_clauses_tptp                false
% 2.10/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.10/1.03  --bmc1_dump_file                        -
% 2.10/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.10/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.10/1.03  --bmc1_ucm_extend_mode                  1
% 2.10/1.03  --bmc1_ucm_init_mode                    2
% 2.10/1.03  --bmc1_ucm_cone_mode                    none
% 2.10/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.10/1.03  --bmc1_ucm_relax_model                  4
% 2.10/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.10/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/1.03  --bmc1_ucm_layered_model                none
% 2.10/1.03  --bmc1_ucm_max_lemma_size               10
% 2.10/1.03  
% 2.10/1.03  ------ AIG Options
% 2.10/1.03  
% 2.10/1.03  --aig_mode                              false
% 2.10/1.03  
% 2.10/1.03  ------ Instantiation Options
% 2.10/1.03  
% 2.10/1.03  --instantiation_flag                    true
% 2.10/1.03  --inst_sos_flag                         false
% 2.10/1.03  --inst_sos_phase                        true
% 2.10/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/1.03  --inst_lit_sel_side                     num_symb
% 2.10/1.03  --inst_solver_per_active                1400
% 2.10/1.03  --inst_solver_calls_frac                1.
% 2.10/1.03  --inst_passive_queue_type               priority_queues
% 2.10/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/1.03  --inst_passive_queues_freq              [25;2]
% 2.10/1.03  --inst_dismatching                      true
% 2.10/1.03  --inst_eager_unprocessed_to_passive     true
% 2.10/1.03  --inst_prop_sim_given                   true
% 2.10/1.03  --inst_prop_sim_new                     false
% 2.10/1.03  --inst_subs_new                         false
% 2.10/1.03  --inst_eq_res_simp                      false
% 2.10/1.03  --inst_subs_given                       false
% 2.10/1.03  --inst_orphan_elimination               true
% 2.10/1.03  --inst_learning_loop_flag               true
% 2.10/1.03  --inst_learning_start                   3000
% 2.10/1.03  --inst_learning_factor                  2
% 2.10/1.03  --inst_start_prop_sim_after_learn       3
% 2.10/1.03  --inst_sel_renew                        solver
% 2.10/1.03  --inst_lit_activity_flag                true
% 2.10/1.03  --inst_restr_to_given                   false
% 2.10/1.03  --inst_activity_threshold               500
% 2.10/1.03  --inst_out_proof                        true
% 2.10/1.03  
% 2.10/1.03  ------ Resolution Options
% 2.10/1.03  
% 2.10/1.03  --resolution_flag                       true
% 2.10/1.03  --res_lit_sel                           adaptive
% 2.10/1.03  --res_lit_sel_side                      none
% 2.10/1.03  --res_ordering                          kbo
% 2.10/1.03  --res_to_prop_solver                    active
% 2.10/1.03  --res_prop_simpl_new                    false
% 2.10/1.03  --res_prop_simpl_given                  true
% 2.10/1.03  --res_passive_queue_type                priority_queues
% 2.10/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/1.03  --res_passive_queues_freq               [15;5]
% 2.10/1.03  --res_forward_subs                      full
% 2.10/1.03  --res_backward_subs                     full
% 2.10/1.03  --res_forward_subs_resolution           true
% 2.10/1.03  --res_backward_subs_resolution          true
% 2.10/1.03  --res_orphan_elimination                true
% 2.10/1.03  --res_time_limit                        2.
% 2.10/1.03  --res_out_proof                         true
% 2.10/1.03  
% 2.10/1.03  ------ Superposition Options
% 2.10/1.03  
% 2.10/1.03  --superposition_flag                    true
% 2.10/1.03  --sup_passive_queue_type                priority_queues
% 2.10/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.10/1.03  --demod_completeness_check              fast
% 2.10/1.03  --demod_use_ground                      true
% 2.10/1.03  --sup_to_prop_solver                    passive
% 2.10/1.03  --sup_prop_simpl_new                    true
% 2.10/1.03  --sup_prop_simpl_given                  true
% 2.10/1.03  --sup_fun_splitting                     false
% 2.10/1.03  --sup_smt_interval                      50000
% 2.10/1.03  
% 2.10/1.03  ------ Superposition Simplification Setup
% 2.10/1.03  
% 2.10/1.03  --sup_indices_passive                   []
% 2.10/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.03  --sup_full_bw                           [BwDemod]
% 2.10/1.03  --sup_immed_triv                        [TrivRules]
% 2.10/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.03  --sup_immed_bw_main                     []
% 2.10/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.03  
% 2.10/1.03  ------ Combination Options
% 2.10/1.03  
% 2.10/1.03  --comb_res_mult                         3
% 2.10/1.03  --comb_sup_mult                         2
% 2.10/1.03  --comb_inst_mult                        10
% 2.10/1.03  
% 2.10/1.03  ------ Debug Options
% 2.10/1.03  
% 2.10/1.03  --dbg_backtrace                         false
% 2.10/1.03  --dbg_dump_prop_clauses                 false
% 2.10/1.03  --dbg_dump_prop_clauses_file            -
% 2.10/1.03  --dbg_out_stat                          false
% 2.10/1.03  ------ Parsing...
% 2.10/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.10/1.03  
% 2.10/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.10/1.03  
% 2.10/1.03  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.10/1.03  
% 2.10/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.10/1.03  ------ Proving...
% 2.10/1.03  ------ Problem Properties 
% 2.10/1.03  
% 2.10/1.03  
% 2.10/1.03  clauses                                 31
% 2.10/1.03  conjectures                             2
% 2.10/1.03  EPR                                     3
% 2.10/1.03  Horn                                    19
% 2.10/1.03  unary                                   4
% 2.10/1.03  binary                                  5
% 2.10/1.03  lits                                    85
% 2.10/1.03  lits eq                                 22
% 2.10/1.03  fd_pure                                 0
% 2.10/1.03  fd_pseudo                               0
% 2.10/1.03  fd_cond                                 3
% 2.10/1.03  fd_pseudo_cond                          0
% 2.10/1.03  AC symbols                              0
% 2.10/1.03  
% 2.10/1.03  ------ Schedule dynamic 5 is on 
% 2.10/1.03  
% 2.10/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.10/1.03  
% 2.10/1.03  
% 2.10/1.03  ------ 
% 2.10/1.03  Current options:
% 2.10/1.03  ------ 
% 2.10/1.03  
% 2.10/1.03  ------ Input Options
% 2.10/1.03  
% 2.10/1.03  --out_options                           all
% 2.10/1.03  --tptp_safe_out                         true
% 2.10/1.03  --problem_path                          ""
% 2.10/1.03  --include_path                          ""
% 2.10/1.03  --clausifier                            res/vclausify_rel
% 2.10/1.03  --clausifier_options                    --mode clausify
% 2.10/1.03  --stdin                                 false
% 2.10/1.03  --stats_out                             all
% 2.10/1.03  
% 2.10/1.03  ------ General Options
% 2.10/1.03  
% 2.10/1.03  --fof                                   false
% 2.10/1.03  --time_out_real                         305.
% 2.10/1.03  --time_out_virtual                      -1.
% 2.10/1.03  --symbol_type_check                     false
% 2.10/1.03  --clausify_out                          false
% 2.10/1.03  --sig_cnt_out                           false
% 2.10/1.03  --trig_cnt_out                          false
% 2.10/1.03  --trig_cnt_out_tolerance                1.
% 2.10/1.03  --trig_cnt_out_sk_spl                   false
% 2.10/1.03  --abstr_cl_out                          false
% 2.10/1.03  
% 2.10/1.03  ------ Global Options
% 2.10/1.03  
% 2.10/1.03  --schedule                              default
% 2.10/1.03  --add_important_lit                     false
% 2.10/1.03  --prop_solver_per_cl                    1000
% 2.10/1.03  --min_unsat_core                        false
% 2.10/1.03  --soft_assumptions                      false
% 2.10/1.03  --soft_lemma_size                       3
% 2.10/1.03  --prop_impl_unit_size                   0
% 2.10/1.03  --prop_impl_unit                        []
% 2.10/1.03  --share_sel_clauses                     true
% 2.10/1.03  --reset_solvers                         false
% 2.10/1.03  --bc_imp_inh                            [conj_cone]
% 2.10/1.03  --conj_cone_tolerance                   3.
% 2.10/1.03  --extra_neg_conj                        none
% 2.10/1.03  --large_theory_mode                     true
% 2.10/1.03  --prolific_symb_bound                   200
% 2.10/1.03  --lt_threshold                          2000
% 2.10/1.03  --clause_weak_htbl                      true
% 2.10/1.03  --gc_record_bc_elim                     false
% 2.10/1.03  
% 2.10/1.03  ------ Preprocessing Options
% 2.10/1.03  
% 2.10/1.03  --preprocessing_flag                    true
% 2.10/1.03  --time_out_prep_mult                    0.1
% 2.10/1.03  --splitting_mode                        input
% 2.10/1.03  --splitting_grd                         true
% 2.10/1.03  --splitting_cvd                         false
% 2.10/1.03  --splitting_cvd_svl                     false
% 2.10/1.03  --splitting_nvd                         32
% 2.10/1.03  --sub_typing                            true
% 2.10/1.03  --prep_gs_sim                           true
% 2.10/1.03  --prep_unflatten                        true
% 2.10/1.03  --prep_res_sim                          true
% 2.10/1.03  --prep_upred                            true
% 2.10/1.03  --prep_sem_filter                       exhaustive
% 2.10/1.03  --prep_sem_filter_out                   false
% 2.10/1.03  --pred_elim                             true
% 2.10/1.03  --res_sim_input                         true
% 2.10/1.03  --eq_ax_congr_red                       true
% 2.10/1.03  --pure_diseq_elim                       true
% 2.10/1.03  --brand_transform                       false
% 2.10/1.03  --non_eq_to_eq                          false
% 2.10/1.03  --prep_def_merge                        true
% 2.10/1.03  --prep_def_merge_prop_impl              false
% 2.10/1.03  --prep_def_merge_mbd                    true
% 2.10/1.03  --prep_def_merge_tr_red                 false
% 2.10/1.03  --prep_def_merge_tr_cl                  false
% 2.10/1.03  --smt_preprocessing                     true
% 2.10/1.03  --smt_ac_axioms                         fast
% 2.10/1.03  --preprocessed_out                      false
% 2.10/1.03  --preprocessed_stats                    false
% 2.10/1.03  
% 2.10/1.03  ------ Abstraction refinement Options
% 2.10/1.03  
% 2.10/1.03  --abstr_ref                             []
% 2.10/1.03  --abstr_ref_prep                        false
% 2.10/1.03  --abstr_ref_until_sat                   false
% 2.10/1.03  --abstr_ref_sig_restrict                funpre
% 2.10/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/1.03  --abstr_ref_under                       []
% 2.10/1.03  
% 2.10/1.03  ------ SAT Options
% 2.10/1.03  
% 2.10/1.03  --sat_mode                              false
% 2.10/1.03  --sat_fm_restart_options                ""
% 2.10/1.03  --sat_gr_def                            false
% 2.10/1.03  --sat_epr_types                         true
% 2.10/1.03  --sat_non_cyclic_types                  false
% 2.10/1.03  --sat_finite_models                     false
% 2.10/1.03  --sat_fm_lemmas                         false
% 2.10/1.03  --sat_fm_prep                           false
% 2.10/1.03  --sat_fm_uc_incr                        true
% 2.10/1.03  --sat_out_model                         small
% 2.10/1.03  --sat_out_clauses                       false
% 2.10/1.03  
% 2.10/1.03  ------ QBF Options
% 2.10/1.03  
% 2.10/1.03  --qbf_mode                              false
% 2.10/1.03  --qbf_elim_univ                         false
% 2.10/1.03  --qbf_dom_inst                          none
% 2.10/1.03  --qbf_dom_pre_inst                      false
% 2.10/1.03  --qbf_sk_in                             false
% 2.10/1.03  --qbf_pred_elim                         true
% 2.10/1.03  --qbf_split                             512
% 2.10/1.03  
% 2.10/1.03  ------ BMC1 Options
% 2.10/1.03  
% 2.10/1.03  --bmc1_incremental                      false
% 2.10/1.03  --bmc1_axioms                           reachable_all
% 2.10/1.03  --bmc1_min_bound                        0
% 2.10/1.03  --bmc1_max_bound                        -1
% 2.10/1.03  --bmc1_max_bound_default                -1
% 2.10/1.03  --bmc1_symbol_reachability              true
% 2.10/1.03  --bmc1_property_lemmas                  false
% 2.10/1.03  --bmc1_k_induction                      false
% 2.10/1.03  --bmc1_non_equiv_states                 false
% 2.10/1.03  --bmc1_deadlock                         false
% 2.10/1.03  --bmc1_ucm                              false
% 2.10/1.03  --bmc1_add_unsat_core                   none
% 2.10/1.03  --bmc1_unsat_core_children              false
% 2.10/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/1.03  --bmc1_out_stat                         full
% 2.10/1.03  --bmc1_ground_init                      false
% 2.10/1.03  --bmc1_pre_inst_next_state              false
% 2.10/1.03  --bmc1_pre_inst_state                   false
% 2.10/1.03  --bmc1_pre_inst_reach_state             false
% 2.10/1.03  --bmc1_out_unsat_core                   false
% 2.10/1.03  --bmc1_aig_witness_out                  false
% 2.10/1.03  --bmc1_verbose                          false
% 2.10/1.03  --bmc1_dump_clauses_tptp                false
% 2.10/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.10/1.03  --bmc1_dump_file                        -
% 2.10/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.10/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.10/1.03  --bmc1_ucm_extend_mode                  1
% 2.10/1.03  --bmc1_ucm_init_mode                    2
% 2.10/1.03  --bmc1_ucm_cone_mode                    none
% 2.10/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.10/1.03  --bmc1_ucm_relax_model                  4
% 2.10/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.10/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/1.03  --bmc1_ucm_layered_model                none
% 2.10/1.03  --bmc1_ucm_max_lemma_size               10
% 2.10/1.03  
% 2.10/1.03  ------ AIG Options
% 2.10/1.03  
% 2.10/1.03  --aig_mode                              false
% 2.10/1.03  
% 2.10/1.03  ------ Instantiation Options
% 2.10/1.03  
% 2.10/1.03  --instantiation_flag                    true
% 2.10/1.03  --inst_sos_flag                         false
% 2.10/1.03  --inst_sos_phase                        true
% 2.10/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/1.03  --inst_lit_sel_side                     none
% 2.10/1.03  --inst_solver_per_active                1400
% 2.10/1.03  --inst_solver_calls_frac                1.
% 2.10/1.03  --inst_passive_queue_type               priority_queues
% 2.10/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/1.03  --inst_passive_queues_freq              [25;2]
% 2.10/1.03  --inst_dismatching                      true
% 2.10/1.03  --inst_eager_unprocessed_to_passive     true
% 2.10/1.03  --inst_prop_sim_given                   true
% 2.10/1.03  --inst_prop_sim_new                     false
% 2.10/1.03  --inst_subs_new                         false
% 2.10/1.03  --inst_eq_res_simp                      false
% 2.10/1.03  --inst_subs_given                       false
% 2.10/1.03  --inst_orphan_elimination               true
% 2.10/1.03  --inst_learning_loop_flag               true
% 2.10/1.03  --inst_learning_start                   3000
% 2.10/1.03  --inst_learning_factor                  2
% 2.10/1.03  --inst_start_prop_sim_after_learn       3
% 2.10/1.03  --inst_sel_renew                        solver
% 2.10/1.03  --inst_lit_activity_flag                true
% 2.10/1.03  --inst_restr_to_given                   false
% 2.10/1.03  --inst_activity_threshold               500
% 2.10/1.03  --inst_out_proof                        true
% 2.10/1.03  
% 2.10/1.03  ------ Resolution Options
% 2.10/1.03  
% 2.10/1.03  --resolution_flag                       false
% 2.10/1.03  --res_lit_sel                           adaptive
% 2.10/1.03  --res_lit_sel_side                      none
% 2.10/1.03  --res_ordering                          kbo
% 2.10/1.03  --res_to_prop_solver                    active
% 2.10/1.03  --res_prop_simpl_new                    false
% 2.10/1.03  --res_prop_simpl_given                  true
% 2.10/1.03  --res_passive_queue_type                priority_queues
% 2.10/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/1.03  --res_passive_queues_freq               [15;5]
% 2.10/1.03  --res_forward_subs                      full
% 2.10/1.03  --res_backward_subs                     full
% 2.10/1.03  --res_forward_subs_resolution           true
% 2.10/1.03  --res_backward_subs_resolution          true
% 2.10/1.03  --res_orphan_elimination                true
% 2.10/1.03  --res_time_limit                        2.
% 2.10/1.03  --res_out_proof                         true
% 2.10/1.03  
% 2.10/1.03  ------ Superposition Options
% 2.10/1.03  
% 2.10/1.03  --superposition_flag                    true
% 2.10/1.03  --sup_passive_queue_type                priority_queues
% 2.10/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.10/1.03  --demod_completeness_check              fast
% 2.10/1.03  --demod_use_ground                      true
% 2.10/1.03  --sup_to_prop_solver                    passive
% 2.10/1.03  --sup_prop_simpl_new                    true
% 2.10/1.03  --sup_prop_simpl_given                  true
% 2.10/1.03  --sup_fun_splitting                     false
% 2.10/1.03  --sup_smt_interval                      50000
% 2.10/1.03  
% 2.10/1.03  ------ Superposition Simplification Setup
% 2.10/1.03  
% 2.10/1.03  --sup_indices_passive                   []
% 2.10/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.03  --sup_full_bw                           [BwDemod]
% 2.10/1.03  --sup_immed_triv                        [TrivRules]
% 2.10/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.03  --sup_immed_bw_main                     []
% 2.10/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.03  
% 2.10/1.03  ------ Combination Options
% 2.10/1.03  
% 2.10/1.03  --comb_res_mult                         3
% 2.10/1.03  --comb_sup_mult                         2
% 2.10/1.03  --comb_inst_mult                        10
% 2.10/1.03  
% 2.10/1.03  ------ Debug Options
% 2.10/1.03  
% 2.10/1.03  --dbg_backtrace                         false
% 2.10/1.03  --dbg_dump_prop_clauses                 false
% 2.10/1.03  --dbg_dump_prop_clauses_file            -
% 2.10/1.03  --dbg_out_stat                          false
% 2.10/1.03  
% 2.10/1.03  
% 2.10/1.03  
% 2.10/1.03  
% 2.10/1.03  ------ Proving...
% 2.10/1.03  
% 2.10/1.03  
% 2.10/1.03  % SZS status Theorem for theBenchmark.p
% 2.10/1.03  
% 2.10/1.03   Resolution empty clause
% 2.10/1.03  
% 2.10/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.10/1.03  
% 2.10/1.03  fof(f2,axiom,(
% 2.10/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.03  
% 2.10/1.03  fof(f14,plain,(
% 2.10/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.10/1.03    inference(ennf_transformation,[],[f2])).
% 2.10/1.03  
% 2.10/1.03  fof(f37,plain,(
% 2.10/1.03    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.10/1.03    inference(cnf_transformation,[],[f14])).
% 2.10/1.03  
% 2.10/1.03  fof(f10,axiom,(
% 2.10/1.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.03  
% 2.10/1.03  fof(f24,plain,(
% 2.10/1.03    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.10/1.03    inference(ennf_transformation,[],[f10])).
% 2.10/1.03  
% 2.10/1.03  fof(f25,plain,(
% 2.10/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.10/1.03    inference(flattening,[],[f24])).
% 2.10/1.03  
% 2.10/1.03  fof(f30,plain,(
% 2.10/1.03    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 2.10/1.03    introduced(choice_axiom,[])).
% 2.10/1.03  
% 2.10/1.03  fof(f31,plain,(
% 2.10/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.10/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f30])).
% 2.10/1.03  
% 2.10/1.03  fof(f55,plain,(
% 2.10/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.10/1.03    inference(cnf_transformation,[],[f31])).
% 2.10/1.03  
% 2.10/1.03  fof(f70,plain,(
% 2.10/1.03    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.10/1.03    inference(equality_resolution,[],[f55])).
% 2.10/1.03  
% 2.10/1.03  fof(f11,conjecture,(
% 2.10/1.03    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 2.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.03  
% 2.10/1.03  fof(f12,negated_conjecture,(
% 2.10/1.03    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 2.10/1.03    inference(negated_conjecture,[],[f11])).
% 2.10/1.03  
% 2.10/1.03  fof(f26,plain,(
% 2.10/1.03    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 2.10/1.03    inference(ennf_transformation,[],[f12])).
% 2.10/1.03  
% 2.10/1.03  fof(f27,plain,(
% 2.10/1.03    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 2.10/1.03    inference(flattening,[],[f26])).
% 2.10/1.03  
% 2.10/1.03  fof(f34,plain,(
% 2.10/1.03    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK4),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 2.10/1.03    introduced(choice_axiom,[])).
% 2.10/1.03  
% 2.10/1.03  fof(f33,plain,(
% 2.10/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK3,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) & v1_funct_2(X3,X1,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))) )),
% 2.10/1.03    introduced(choice_axiom,[])).
% 2.10/1.03  
% 2.10/1.03  fof(f32,plain,(
% 2.10/1.03    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK2,X2,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_2(X3,sK2,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))),
% 2.10/1.03    introduced(choice_axiom,[])).
% 2.10/1.03  
% 2.10/1.03  fof(f35,plain,(
% 2.10/1.03    ((~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 2.10/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f34,f33,f32])).
% 2.10/1.03  
% 2.10/1.03  fof(f59,plain,(
% 2.10/1.03    v1_funct_1(sK4)),
% 2.10/1.03    inference(cnf_transformation,[],[f35])).
% 2.10/1.03  
% 2.10/1.03  fof(f61,plain,(
% 2.10/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.10/1.03    inference(cnf_transformation,[],[f35])).
% 2.10/1.03  
% 2.10/1.03  fof(f4,axiom,(
% 2.10/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.03  
% 2.10/1.03  fof(f16,plain,(
% 2.10/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.03    inference(ennf_transformation,[],[f4])).
% 2.10/1.03  
% 2.10/1.03  fof(f40,plain,(
% 2.10/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.03    inference(cnf_transformation,[],[f16])).
% 2.10/1.03  
% 2.10/1.03  fof(f8,axiom,(
% 2.10/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.03  
% 2.10/1.03  fof(f20,plain,(
% 2.10/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.03    inference(ennf_transformation,[],[f8])).
% 2.10/1.03  
% 2.10/1.03  fof(f21,plain,(
% 2.10/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.03    inference(flattening,[],[f20])).
% 2.10/1.03  
% 2.10/1.03  fof(f29,plain,(
% 2.10/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.03    inference(nnf_transformation,[],[f21])).
% 2.10/1.03  
% 2.10/1.03  fof(f44,plain,(
% 2.10/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.03    inference(cnf_transformation,[],[f29])).
% 2.10/1.03  
% 2.10/1.03  fof(f6,axiom,(
% 2.10/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.03  
% 2.10/1.03  fof(f18,plain,(
% 2.10/1.03    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.03    inference(ennf_transformation,[],[f6])).
% 2.10/1.03  
% 2.10/1.03  fof(f42,plain,(
% 2.10/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.03    inference(cnf_transformation,[],[f18])).
% 2.10/1.03  
% 2.10/1.03  fof(f60,plain,(
% 2.10/1.03    v1_funct_2(sK4,sK2,sK3)),
% 2.10/1.03    inference(cnf_transformation,[],[f35])).
% 2.10/1.03  
% 2.10/1.03  fof(f1,axiom,(
% 2.10/1.03    v1_xboole_0(k1_xboole_0)),
% 2.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.03  
% 2.10/1.03  fof(f36,plain,(
% 2.10/1.03    v1_xboole_0(k1_xboole_0)),
% 2.10/1.03    inference(cnf_transformation,[],[f1])).
% 2.10/1.03  
% 2.10/1.03  fof(f58,plain,(
% 2.10/1.03    ~v1_xboole_0(sK3)),
% 2.10/1.03    inference(cnf_transformation,[],[f35])).
% 2.10/1.03  
% 2.10/1.03  fof(f9,axiom,(
% 2.10/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.03  
% 2.10/1.03  fof(f22,plain,(
% 2.10/1.03    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.10/1.03    inference(ennf_transformation,[],[f9])).
% 2.10/1.03  
% 2.10/1.03  fof(f23,plain,(
% 2.10/1.03    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.10/1.03    inference(flattening,[],[f22])).
% 2.10/1.03  
% 2.10/1.03  fof(f50,plain,(
% 2.10/1.03    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.10/1.03    inference(cnf_transformation,[],[f23])).
% 2.10/1.03  
% 2.10/1.03  fof(f57,plain,(
% 2.10/1.03    ~v1_xboole_0(sK2)),
% 2.10/1.03    inference(cnf_transformation,[],[f35])).
% 2.10/1.03  
% 2.10/1.03  fof(f5,axiom,(
% 2.10/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.03  
% 2.10/1.03  fof(f13,plain,(
% 2.10/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.10/1.03    inference(pure_predicate_removal,[],[f5])).
% 2.10/1.03  
% 2.10/1.03  fof(f17,plain,(
% 2.10/1.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.03    inference(ennf_transformation,[],[f13])).
% 2.10/1.03  
% 2.10/1.03  fof(f41,plain,(
% 2.10/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.03    inference(cnf_transformation,[],[f17])).
% 2.10/1.03  
% 2.10/1.03  fof(f3,axiom,(
% 2.10/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.03  
% 2.10/1.03  fof(f15,plain,(
% 2.10/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.10/1.03    inference(ennf_transformation,[],[f3])).
% 2.10/1.03  
% 2.10/1.03  fof(f28,plain,(
% 2.10/1.03    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.10/1.03    inference(nnf_transformation,[],[f15])).
% 2.10/1.03  
% 2.10/1.03  fof(f38,plain,(
% 2.10/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.10/1.03    inference(cnf_transformation,[],[f28])).
% 2.10/1.03  
% 2.10/1.03  fof(f63,plain,(
% 2.10/1.03    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)),
% 2.10/1.03    inference(cnf_transformation,[],[f35])).
% 2.10/1.03  
% 2.10/1.03  fof(f7,axiom,(
% 2.10/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.03  
% 2.10/1.03  fof(f19,plain,(
% 2.10/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.03    inference(ennf_transformation,[],[f7])).
% 2.10/1.03  
% 2.10/1.03  fof(f43,plain,(
% 2.10/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.03    inference(cnf_transformation,[],[f19])).
% 2.10/1.03  
% 2.10/1.03  fof(f62,plain,(
% 2.10/1.03    ( ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) )),
% 2.10/1.03    inference(cnf_transformation,[],[f35])).
% 2.10/1.03  
% 2.10/1.03  fof(f56,plain,(
% 2.10/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.10/1.03    inference(cnf_transformation,[],[f31])).
% 2.10/1.03  
% 2.10/1.03  fof(f69,plain,(
% 2.10/1.03    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.10/1.03    inference(equality_resolution,[],[f56])).
% 2.10/1.03  
% 2.10/1.03  fof(f54,plain,(
% 2.10/1.03    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.10/1.03    inference(cnf_transformation,[],[f31])).
% 2.10/1.03  
% 2.10/1.03  fof(f71,plain,(
% 2.10/1.03    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.10/1.03    inference(equality_resolution,[],[f54])).
% 2.10/1.03  
% 2.10/1.03  cnf(c_1,plain,
% 2.10/1.03      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.10/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_16,plain,
% 2.10/1.03      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 2.10/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.10/1.03      | ~ v1_funct_1(X0)
% 2.10/1.03      | ~ v1_relat_1(X0) ),
% 2.10/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_25,negated_conjecture,
% 2.10/1.03      ( v1_funct_1(sK4) ),
% 2.10/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_556,plain,
% 2.10/1.03      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 2.10/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.10/1.03      | ~ v1_relat_1(X0)
% 2.10/1.03      | sK4 != X0 ),
% 2.10/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_557,plain,
% 2.10/1.03      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 2.10/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 2.10/1.03      | ~ v1_relat_1(sK4) ),
% 2.10/1.03      inference(unflattening,[status(thm)],[c_556]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_696,plain,
% 2.10/1.03      ( m1_subset_1(X0,X1)
% 2.10/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X2)))
% 2.10/1.03      | ~ v1_relat_1(sK4)
% 2.10/1.03      | sK0(k1_relat_1(sK4),X2,sK4) != X0
% 2.10/1.03      | k1_relat_1(sK4) != X1 ),
% 2.10/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_557]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_697,plain,
% 2.10/1.03      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 2.10/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 2.10/1.03      | ~ v1_relat_1(sK4) ),
% 2.10/1.03      inference(unflattening,[status(thm)],[c_696]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_1829,plain,
% 2.10/1.03      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 2.10/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 2.10/1.03      | v1_relat_1(sK4) != iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_23,negated_conjecture,
% 2.10/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.10/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_32,plain,
% 2.10/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_698,plain,
% 2.10/1.03      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 2.10/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 2.10/1.03      | v1_relat_1(sK4) != iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_4,plain,
% 2.10/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.10/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_2058,plain,
% 2.10/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.10/1.03      | v1_relat_1(sK4) ),
% 2.10/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_2059,plain,
% 2.10/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.10/1.03      | v1_relat_1(sK4) = iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_2058]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_3786,plain,
% 2.10/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 2.10/1.03      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top ),
% 2.10/1.03      inference(global_propositional_subsumption,
% 2.10/1.03                [status(thm)],
% 2.10/1.03                [c_1829,c_32,c_698,c_2059]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_3787,plain,
% 2.10/1.03      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 2.10/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 2.10/1.03      inference(renaming,[status(thm)],[c_3786]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_1835,plain,
% 2.10/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_13,plain,
% 2.10/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.10/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.10/1.03      | k1_xboole_0 = X2 ),
% 2.10/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_1836,plain,
% 2.10/1.03      ( k1_relset_1(X0,X1,X2) = X0
% 2.10/1.03      | k1_xboole_0 = X1
% 2.10/1.03      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.10/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_2875,plain,
% 2.10/1.03      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 2.10/1.03      | sK3 = k1_xboole_0
% 2.10/1.03      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 2.10/1.03      inference(superposition,[status(thm)],[c_1835,c_1836]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_6,plain,
% 2.10/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.10/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_1843,plain,
% 2.10/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.10/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_2270,plain,
% 2.10/1.03      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.10/1.03      inference(superposition,[status(thm)],[c_1835,c_1843]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_2897,plain,
% 2.10/1.03      ( k1_relat_1(sK4) = sK2
% 2.10/1.03      | sK3 = k1_xboole_0
% 2.10/1.03      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 2.10/1.03      inference(demodulation,[status(thm)],[c_2875,c_2270]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_24,negated_conjecture,
% 2.10/1.03      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.10/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_31,plain,
% 2.10/1.03      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_0,plain,
% 2.10/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 2.10/1.03      inference(cnf_transformation,[],[f36]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_26,negated_conjecture,
% 2.10/1.03      ( ~ v1_xboole_0(sK3) ),
% 2.10/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_342,plain,
% 2.10/1.03      ( sK3 != k1_xboole_0 ),
% 2.10/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_26]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_2997,plain,
% 2.10/1.03      ( k1_relat_1(sK4) = sK2 ),
% 2.10/1.03      inference(global_propositional_subsumption,
% 2.10/1.03                [status(thm)],
% 2.10/1.03                [c_2897,c_31,c_342]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_3792,plain,
% 2.10/1.03      ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 2.10/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 2.10/1.03      inference(light_normalisation,[status(thm)],[c_3787,c_2997]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_14,plain,
% 2.10/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.10/1.03      | ~ m1_subset_1(X3,X1)
% 2.10/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.03      | ~ v1_funct_1(X0)
% 2.10/1.03      | v1_xboole_0(X1)
% 2.10/1.03      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.10/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_27,negated_conjecture,
% 2.10/1.03      ( ~ v1_xboole_0(sK2) ),
% 2.10/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_371,plain,
% 2.10/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.10/1.03      | ~ m1_subset_1(X3,X1)
% 2.10/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.03      | ~ v1_funct_1(X0)
% 2.10/1.03      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 2.10/1.03      | sK2 != X1 ),
% 2.10/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_372,plain,
% 2.10/1.03      ( ~ v1_funct_2(X0,sK2,X1)
% 2.10/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 2.10/1.03      | ~ m1_subset_1(X2,sK2)
% 2.10/1.03      | ~ v1_funct_1(X0)
% 2.10/1.03      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.10/1.03      inference(unflattening,[status(thm)],[c_371]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_490,plain,
% 2.10/1.03      ( ~ v1_funct_2(X0,sK2,X1)
% 2.10/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 2.10/1.03      | ~ m1_subset_1(X2,sK2)
% 2.10/1.03      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
% 2.10/1.03      | sK4 != X0 ),
% 2.10/1.03      inference(resolution_lifted,[status(thm)],[c_372,c_25]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_491,plain,
% 2.10/1.03      ( ~ v1_funct_2(sK4,sK2,X0)
% 2.10/1.03      | ~ m1_subset_1(X1,sK2)
% 2.10/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.10/1.03      | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
% 2.10/1.03      inference(unflattening,[status(thm)],[c_490]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_1832,plain,
% 2.10/1.03      ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 2.10/1.03      | v1_funct_2(sK4,sK2,X0) != iProver_top
% 2.10/1.03      | m1_subset_1(X1,sK2) != iProver_top
% 2.10/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_2098,plain,
% 2.10/1.03      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 2.10/1.03      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 2.10/1.03      | m1_subset_1(X0,sK2) != iProver_top ),
% 2.10/1.03      inference(superposition,[status(thm)],[c_1835,c_1832]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_2405,plain,
% 2.10/1.03      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 2.10/1.03      | m1_subset_1(X0,sK2) != iProver_top ),
% 2.10/1.03      inference(global_propositional_subsumption,[status(thm)],[c_2098,c_31]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_3798,plain,
% 2.10/1.03      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 2.10/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 2.10/1.03      inference(superposition,[status(thm)],[c_3792,c_2405]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_5,plain,
% 2.10/1.03      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.10/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_3,plain,
% 2.10/1.03      ( r1_tarski(k2_relat_1(X0),X1) | ~ v5_relat_1(X0,X1) | ~ v1_relat_1(X0) ),
% 2.10/1.03      inference(cnf_transformation,[],[f38]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_21,negated_conjecture,
% 2.10/1.03      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
% 2.10/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_303,plain,
% 2.10/1.03      ( ~ v5_relat_1(X0,X1)
% 2.10/1.03      | ~ v1_relat_1(X0)
% 2.10/1.03      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0)
% 2.10/1.03      | sK1 != X1 ),
% 2.10/1.03      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_304,plain,
% 2.10/1.03      ( ~ v5_relat_1(X0,sK1)
% 2.10/1.03      | ~ v1_relat_1(X0)
% 2.10/1.03      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0) ),
% 2.10/1.03      inference(unflattening,[status(thm)],[c_303]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_322,plain,
% 2.10/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.03      | ~ v1_relat_1(X3)
% 2.10/1.03      | X3 != X0
% 2.10/1.03      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X3)
% 2.10/1.03      | sK1 != X2 ),
% 2.10/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_304]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_323,plain,
% 2.10/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 2.10/1.03      | ~ v1_relat_1(X0)
% 2.10/1.03      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0) ),
% 2.10/1.03      inference(unflattening,[status(thm)],[c_322]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_333,plain,
% 2.10/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 2.10/1.03      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0) ),
% 2.10/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_323,c_4]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_1833,plain,
% 2.10/1.03      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(X0)
% 2.10/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_333]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_7,plain,
% 2.10/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.10/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_1842,plain,
% 2.10/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.10/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_2266,plain,
% 2.10/1.03      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 2.10/1.03      inference(superposition,[status(thm)],[c_1835,c_1842]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_4100,plain,
% 2.10/1.03      ( k2_relat_1(X0) != k2_relat_1(sK4)
% 2.10/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top ),
% 2.10/1.03      inference(light_normalisation,[status(thm)],[c_1833,c_2266]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_4106,plain,
% 2.10/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top ),
% 2.10/1.03      inference(equality_resolution,[status(thm)],[c_4100]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_4224,plain,
% 2.10/1.03      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4)) ),
% 2.10/1.03      inference(superposition,[status(thm)],[c_3798,c_4106]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_22,negated_conjecture,
% 2.10/1.03      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1) | ~ m1_subset_1(X0,sK2) ),
% 2.10/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_684,plain,
% 2.10/1.03      ( m1_subset_1(X0,X1)
% 2.10/1.03      | ~ m1_subset_1(X2,sK2)
% 2.10/1.03      | k3_funct_2(sK2,sK3,sK4,X2) != X0
% 2.10/1.03      | sK1 != X1 ),
% 2.10/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_22]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_685,plain,
% 2.10/1.03      ( ~ m1_subset_1(X0,sK2) | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) ),
% 2.10/1.03      inference(unflattening,[status(thm)],[c_684]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_1830,plain,
% 2.10/1.03      ( m1_subset_1(X0,sK2) != iProver_top
% 2.10/1.03      | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_685]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_4387,plain,
% 2.10/1.03      ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 2.10/1.03      | m1_subset_1(k1_funct_1(sK4,sK0(sK2,sK1,sK4)),sK1) = iProver_top ),
% 2.10/1.03      inference(superposition,[status(thm)],[c_4224,c_1830]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_15,plain,
% 2.10/1.03      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 2.10/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.10/1.03      | ~ v1_funct_1(X0)
% 2.10/1.03      | ~ v1_relat_1(X0) ),
% 2.10/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_571,plain,
% 2.10/1.03      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 2.10/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.10/1.03      | ~ v1_relat_1(X0)
% 2.10/1.03      | sK4 != X0 ),
% 2.10/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_572,plain,
% 2.10/1.03      ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 2.10/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 2.10/1.03      | ~ v1_relat_1(sK4) ),
% 2.10/1.03      inference(unflattening,[status(thm)],[c_571]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_726,plain,
% 2.10/1.03      ( ~ m1_subset_1(X0,sK2)
% 2.10/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
% 2.10/1.03      | ~ v1_relat_1(sK4)
% 2.10/1.03      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 2.10/1.03      | sK1 != X1 ),
% 2.10/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_572]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_727,plain,
% 2.10/1.03      ( ~ m1_subset_1(X0,sK2)
% 2.10/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 2.10/1.03      | ~ v1_relat_1(sK4)
% 2.10/1.03      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 2.10/1.03      inference(unflattening,[status(thm)],[c_726]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_1360,plain,
% 2.10/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 2.10/1.03      | ~ v1_relat_1(sK4)
% 2.10/1.03      | sP2_iProver_split ),
% 2.10/1.03      inference(splitting,
% 2.10/1.03                [splitting(split),new_symbols(definition,[])],
% 2.10/1.03                [c_727]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_1826,plain,
% 2.10/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 2.10/1.03      | v1_relat_1(sK4) != iProver_top
% 2.10/1.03      | sP2_iProver_split = iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_1360]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_1404,plain,
% 2.10/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 2.10/1.03      | v1_relat_1(sK4) != iProver_top
% 2.10/1.03      | sP2_iProver_split = iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_1360]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_2486,plain,
% 2.10/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 2.10/1.03      | sP2_iProver_split = iProver_top ),
% 2.10/1.03      inference(global_propositional_subsumption,
% 2.10/1.03                [status(thm)],
% 2.10/1.03                [c_1826,c_32,c_1404,c_2059]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_3005,plain,
% 2.10/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
% 2.10/1.03      | sP2_iProver_split = iProver_top ),
% 2.10/1.03      inference(demodulation,[status(thm)],[c_2997,c_2486]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_4225,plain,
% 2.10/1.03      ( sP2_iProver_split = iProver_top ),
% 2.10/1.03      inference(superposition,[status(thm)],[c_3005,c_4106]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_17,plain,
% 2.10/1.03      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.10/1.03      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 2.10/1.03      | ~ v1_funct_1(X0)
% 2.10/1.03      | ~ v1_relat_1(X0) ),
% 2.10/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_541,plain,
% 2.10/1.03      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.10/1.03      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 2.10/1.03      | ~ v1_relat_1(X0)
% 2.10/1.03      | sK4 != X0 ),
% 2.10/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_542,plain,
% 2.10/1.03      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 2.10/1.03      | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 2.10/1.03      | ~ v1_relat_1(sK4) ),
% 2.10/1.03      inference(unflattening,[status(thm)],[c_541]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_744,plain,
% 2.10/1.03      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 2.10/1.03      | ~ m1_subset_1(X1,sK2)
% 2.10/1.03      | ~ v1_relat_1(sK4)
% 2.10/1.03      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)) != k3_funct_2(sK2,sK3,sK4,X1)
% 2.10/1.03      | sK1 != X0 ),
% 2.10/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_542]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_745,plain,
% 2.10/1.03      ( v1_funct_2(sK4,k1_relat_1(sK4),sK1)
% 2.10/1.03      | ~ m1_subset_1(X0,sK2)
% 2.10/1.03      | ~ v1_relat_1(sK4)
% 2.10/1.03      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 2.10/1.03      inference(unflattening,[status(thm)],[c_744]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_1358,plain,
% 2.10/1.03      ( ~ m1_subset_1(X0,sK2)
% 2.10/1.03      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 2.10/1.03      | ~ sP2_iProver_split ),
% 2.10/1.03      inference(splitting,
% 2.10/1.03                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.10/1.03                [c_745]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_1825,plain,
% 2.10/1.03      ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 2.10/1.03      | m1_subset_1(X0,sK2) != iProver_top
% 2.10/1.03      | sP2_iProver_split != iProver_top ),
% 2.10/1.03      inference(predicate_to_equality,[status(thm)],[c_1358]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_3009,plain,
% 2.10/1.03      ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 2.10/1.03      | m1_subset_1(X0,sK2) != iProver_top
% 2.10/1.03      | sP2_iProver_split != iProver_top ),
% 2.10/1.03      inference(demodulation,[status(thm)],[c_2997,c_1825]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_4386,plain,
% 2.10/1.03      ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 2.10/1.03      | sP2_iProver_split != iProver_top ),
% 2.10/1.03      inference(superposition,[status(thm)],[c_4224,c_3009]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_4451,plain,
% 2.10/1.03      ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
% 2.10/1.03      inference(global_propositional_subsumption,
% 2.10/1.03                [status(thm)],
% 2.10/1.03                [c_4387,c_4225,c_4386]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_4456,plain,
% 2.10/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 2.10/1.03      inference(superposition,[status(thm)],[c_3792,c_4451]) ).
% 2.10/1.03  
% 2.10/1.03  cnf(c_4511,plain,
% 2.10/1.03      ( $false ),
% 2.10/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_4456,c_4106]) ).
% 2.10/1.03  
% 2.10/1.03  
% 2.10/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.10/1.03  
% 2.10/1.03  ------                               Statistics
% 2.10/1.03  
% 2.10/1.03  ------ General
% 2.10/1.03  
% 2.10/1.03  abstr_ref_over_cycles:                  0
% 2.10/1.03  abstr_ref_under_cycles:                 0
% 2.10/1.03  gc_basic_clause_elim:                   0
% 2.10/1.03  forced_gc_time:                         0
% 2.10/1.03  parsing_time:                           0.008
% 2.10/1.03  unif_index_cands_time:                  0.
% 2.10/1.03  unif_index_add_time:                    0.
% 2.10/1.03  orderings_time:                         0.
% 2.10/1.03  out_proof_time:                         0.01
% 2.10/1.03  total_time:                             0.149
% 2.10/1.03  num_of_symbols:                         56
% 2.10/1.03  num_of_terms:                           3066
% 2.10/1.03  
% 2.10/1.03  ------ Preprocessing
% 2.10/1.03  
% 2.10/1.03  num_of_splits:                          6
% 2.10/1.03  num_of_split_atoms:                     3
% 2.10/1.03  num_of_reused_defs:                     3
% 2.10/1.03  num_eq_ax_congr_red:                    19
% 2.10/1.03  num_of_sem_filtered_clauses:            1
% 2.10/1.03  num_of_subtypes:                        0
% 2.10/1.03  monotx_restored_types:                  0
% 2.10/1.03  sat_num_of_epr_types:                   0
% 2.10/1.03  sat_num_of_non_cyclic_types:            0
% 2.10/1.03  sat_guarded_non_collapsed_types:        0
% 2.10/1.03  num_pure_diseq_elim:                    0
% 2.10/1.03  simp_replaced_by:                       0
% 2.10/1.03  res_preprocessed:                       134
% 2.10/1.03  prep_upred:                             0
% 2.10/1.03  prep_unflattend:                        43
% 2.10/1.03  smt_new_axioms:                         0
% 2.10/1.03  pred_elim_cands:                        3
% 2.10/1.03  pred_elim:                              5
% 2.10/1.03  pred_elim_cl:                           1
% 2.10/1.03  pred_elim_cycles:                       9
% 2.10/1.03  merged_defs:                            0
% 2.10/1.03  merged_defs_ncl:                        0
% 2.10/1.03  bin_hyper_res:                          0
% 2.10/1.03  prep_cycles:                            4
% 2.10/1.03  pred_elim_time:                         0.021
% 2.10/1.03  splitting_time:                         0.
% 2.10/1.03  sem_filter_time:                        0.
% 2.10/1.03  monotx_time:                            0.
% 2.10/1.03  subtype_inf_time:                       0.
% 2.10/1.03  
% 2.10/1.03  ------ Problem properties
% 2.10/1.03  
% 2.10/1.03  clauses:                                31
% 2.10/1.03  conjectures:                            2
% 2.10/1.03  epr:                                    3
% 2.10/1.03  horn:                                   19
% 2.10/1.03  ground:                                 10
% 2.10/1.03  unary:                                  4
% 2.10/1.03  binary:                                 5
% 2.10/1.03  lits:                                   85
% 2.10/1.03  lits_eq:                                22
% 2.10/1.03  fd_pure:                                0
% 2.10/1.03  fd_pseudo:                              0
% 2.10/1.03  fd_cond:                                3
% 2.10/1.03  fd_pseudo_cond:                         0
% 2.10/1.03  ac_symbols:                             0
% 2.10/1.03  
% 2.10/1.03  ------ Propositional Solver
% 2.10/1.03  
% 2.10/1.03  prop_solver_calls:                      27
% 2.10/1.03  prop_fast_solver_calls:                 1118
% 2.10/1.03  smt_solver_calls:                       0
% 2.10/1.03  smt_fast_solver_calls:                  0
% 2.10/1.03  prop_num_of_clauses:                    1166
% 2.10/1.03  prop_preprocess_simplified:             4844
% 2.10/1.03  prop_fo_subsumed:                       24
% 2.10/1.03  prop_solver_time:                       0.
% 2.10/1.03  smt_solver_time:                        0.
% 2.10/1.03  smt_fast_solver_time:                   0.
% 2.10/1.03  prop_fast_solver_time:                  0.
% 2.10/1.03  prop_unsat_core_time:                   0.
% 2.10/1.03  
% 2.10/1.03  ------ QBF
% 2.10/1.03  
% 2.10/1.03  qbf_q_res:                              0
% 2.10/1.03  qbf_num_tautologies:                    0
% 2.10/1.03  qbf_prep_cycles:                        0
% 2.10/1.03  
% 2.10/1.03  ------ BMC1
% 2.10/1.03  
% 2.10/1.03  bmc1_current_bound:                     -1
% 2.10/1.03  bmc1_last_solved_bound:                 -1
% 2.10/1.03  bmc1_unsat_core_size:                   -1
% 2.10/1.03  bmc1_unsat_core_parents_size:           -1
% 2.10/1.03  bmc1_merge_next_fun:                    0
% 2.10/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.10/1.03  
% 2.10/1.03  ------ Instantiation
% 2.10/1.03  
% 2.10/1.03  inst_num_of_clauses:                    346
% 2.10/1.03  inst_num_in_passive:                    13
% 2.10/1.03  inst_num_in_active:                     265
% 2.10/1.03  inst_num_in_unprocessed:                68
% 2.10/1.03  inst_num_of_loops:                      290
% 2.10/1.03  inst_num_of_learning_restarts:          0
% 2.10/1.03  inst_num_moves_active_passive:          22
% 2.10/1.03  inst_lit_activity:                      0
% 2.10/1.03  inst_lit_activity_moves:                0
% 2.10/1.03  inst_num_tautologies:                   0
% 2.10/1.03  inst_num_prop_implied:                  0
% 2.10/1.03  inst_num_existing_simplified:           0
% 2.10/1.03  inst_num_eq_res_simplified:             0
% 2.10/1.03  inst_num_child_elim:                    0
% 2.10/1.03  inst_num_of_dismatching_blockings:      35
% 2.10/1.03  inst_num_of_non_proper_insts:           336
% 2.10/1.03  inst_num_of_duplicates:                 0
% 2.10/1.03  inst_inst_num_from_inst_to_res:         0
% 2.10/1.03  inst_dismatching_checking_time:         0.
% 2.10/1.03  
% 2.10/1.03  ------ Resolution
% 2.10/1.03  
% 2.10/1.03  res_num_of_clauses:                     0
% 2.10/1.03  res_num_in_passive:                     0
% 2.10/1.03  res_num_in_active:                      0
% 2.10/1.03  res_num_of_loops:                       138
% 2.10/1.03  res_forward_subset_subsumed:            36
% 2.10/1.03  res_backward_subset_subsumed:           0
% 2.10/1.03  res_forward_subsumed:                   0
% 2.10/1.03  res_backward_subsumed:                  0
% 2.10/1.03  res_forward_subsumption_resolution:     1
% 2.10/1.03  res_backward_subsumption_resolution:    0
% 2.10/1.03  res_clause_to_clause_subsumption:       102
% 2.10/1.03  res_orphan_elimination:                 0
% 2.10/1.03  res_tautology_del:                      45
% 2.10/1.03  res_num_eq_res_simplified:              0
% 2.10/1.03  res_num_sel_changes:                    0
% 2.10/1.03  res_moves_from_active_to_pass:          0
% 2.10/1.03  
% 2.10/1.03  ------ Superposition
% 2.10/1.03  
% 2.10/1.03  sup_time_total:                         0.
% 2.10/1.03  sup_time_generating:                    0.
% 2.10/1.03  sup_time_sim_full:                      0.
% 2.10/1.03  sup_time_sim_immed:                     0.
% 2.10/1.03  
% 2.10/1.03  sup_num_of_clauses:                     61
% 2.10/1.03  sup_num_in_active:                      44
% 2.10/1.03  sup_num_in_passive:                     17
% 2.10/1.03  sup_num_of_loops:                       56
% 2.10/1.03  sup_fw_superposition:                   18
% 2.10/1.03  sup_bw_superposition:                   30
% 2.10/1.03  sup_immediate_simplified:               11
% 2.10/1.03  sup_given_eliminated:                   0
% 2.10/1.03  comparisons_done:                       0
% 2.10/1.03  comparisons_avoided:                    9
% 2.10/1.03  
% 2.10/1.03  ------ Simplifications
% 2.10/1.03  
% 2.10/1.03  
% 2.10/1.03  sim_fw_subset_subsumed:                 6
% 2.10/1.03  sim_bw_subset_subsumed:                 3
% 2.10/1.03  sim_fw_subsumed:                        1
% 2.10/1.03  sim_bw_subsumed:                        0
% 2.10/1.03  sim_fw_subsumption_res:                 1
% 2.10/1.03  sim_bw_subsumption_res:                 0
% 2.10/1.03  sim_tautology_del:                      0
% 2.10/1.03  sim_eq_tautology_del:                   0
% 2.10/1.03  sim_eq_res_simp:                        0
% 2.10/1.03  sim_fw_demodulated:                     1
% 2.10/1.03  sim_bw_demodulated:                     10
% 2.10/1.03  sim_light_normalised:                   10
% 2.10/1.03  sim_joinable_taut:                      0
% 2.10/1.03  sim_joinable_simp:                      0
% 2.10/1.03  sim_ac_normalised:                      0
% 2.10/1.03  sim_smt_subsumption:                    0
% 2.10/1.03  
%------------------------------------------------------------------------------
