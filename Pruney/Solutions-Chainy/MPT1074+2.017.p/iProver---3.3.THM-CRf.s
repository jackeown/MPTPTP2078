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
% DateTime   : Thu Dec  3 12:10:15 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  191 (1659 expanded)
%              Number of clauses        :  121 ( 633 expanded)
%              Number of leaves         :   21 ( 419 expanded)
%              Depth                    :   26
%              Number of atoms          :  629 (8413 expanded)
%              Number of equality atoms :  227 (1044 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f44,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f33,f43,f42,f41])).

fof(f77,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(nnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f39])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f71])).

fof(f75,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,(
    ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f72])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f70])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1889,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1891,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5780,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_1891])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1898,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3199,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1889,c_1898])).

cnf(c_5802,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5780,c_3199])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6399,plain,
    ( sK3 = k1_xboole_0
    | k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5802,c_38])).

cnf(c_6400,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6399])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_573,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_574,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_641,plain,
    ( m1_subset_1(X0,X1)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X2)))
    | ~ v1_relat_1(sK4)
    | sK0(k1_relat_1(sK4),X2,sK4) != X0
    | k1_relat_1(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_574])).

cnf(c_642,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_1882,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_6407,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6400,c_1882])).

cnf(c_28,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_43,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_108,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_107,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_109,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_114,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2211,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2265,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2268,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2265])).

cnf(c_1099,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2329,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1099])).

cnf(c_1101,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2214,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | k2_relset_1(sK2,sK3,sK4) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_2328,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | k2_relset_1(sK2,sK3,sK4) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2214])).

cnf(c_2486,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    | ~ r1_tarski(k2_relat_1(sK4),sK1)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2328])).

cnf(c_2487,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | sK1 != sK1
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2486])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2261,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK1)
    | r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2875,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(k2_relat_1(sK4),X0)
    | r1_tarski(k2_relat_1(sK4),sK1) ),
    inference(instantiation,[status(thm)],[c_2261])).

cnf(c_2879,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2875])).

cnf(c_2881,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2879])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_10])).

cnf(c_1886,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_5409,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_1886])).

cnf(c_1903,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6134,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5409,c_1903])).

cnf(c_6149,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6134])).

cnf(c_6265,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_6266,plain,
    ( sK3 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6265])).

cnf(c_6268,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6266])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1900,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2525,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_1900])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_260,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_261,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_320,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_261])).

cnf(c_1887,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_7071,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2525,c_1887])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1899,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7367,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7071,c_1899])).

cnf(c_11612,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6407,c_30,c_43,c_108,c_109,c_114,c_2211,c_2268,c_2329,c_2487,c_2881,c_6149,c_6268,c_7367])).

cnf(c_11613,plain,
    ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_11612])).

cnf(c_11621,plain,
    ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11613,c_1900])).

cnf(c_11620,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6400,c_11613])).

cnf(c_11676,plain,
    ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11620,c_30,c_43,c_108,c_109,c_114,c_2211,c_2268,c_2329,c_2487,c_2881,c_6149,c_6268,c_7367])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_474,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_34])).

cnf(c_475,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_507,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ m1_subset_1(X2,sK2)
    | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_475,c_32])).

cnf(c_508,plain,
    ( ~ v1_funct_2(sK4,sK2,X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_1885,plain,
    ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | v1_funct_2(sK4,sK2,X0) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_2230,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_1885])).

cnf(c_2235,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2230,c_38])).

cnf(c_11684,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11676,c_2235])).

cnf(c_12118,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | r1_tarski(k2_relat_1(sK4),X0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_11684,c_1886])).

cnf(c_15646,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) = iProver_top
    | k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12118,c_7367])).

cnf(c_15647,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
    | r1_tarski(k2_relat_1(sK4),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_15646])).

cnf(c_1897,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3003,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1889,c_1897])).

cnf(c_1890,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3374,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3003,c_1890])).

cnf(c_15660,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4)) ),
    inference(superposition,[status(thm)],[c_15647,c_3374])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
    | ~ m1_subset_1(X0,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_629,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,sK2)
    | k3_funct_2(sK2,sK3,sK4,X2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_29])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_1883,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_17247,plain,
    ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | m1_subset_1(k1_funct_1(sK4,sK0(sK2,sK1,sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_15660,c_1883])).

cnf(c_22,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_588,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_589,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_671,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_589])).

cnf(c_672,plain,
    ( ~ m1_subset_1(X0,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_1097,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
    | ~ v1_relat_1(sK4)
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_672])).

cnf(c_1879,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1097])).

cnf(c_5410,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_1886])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_558,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_559,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_689,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ m1_subset_1(X1,sK2)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)) != k3_funct_2(sK2,sK3,sK4,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_559])).

cnf(c_690,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),sK1)
    | ~ m1_subset_1(X0,sK2)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_689])).

cnf(c_1095,plain,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_690])).

cnf(c_1878,plain,
    ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1095])).

cnf(c_6428,plain,
    ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
    | sK3 = k1_xboole_0
    | m1_subset_1(X0,sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_6400,c_1878])).

cnf(c_17245,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_15660,c_6428])).

cnf(c_17268,plain,
    ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17247,c_30,c_43,c_108,c_109,c_114,c_2211,c_2268,c_2329,c_2487,c_2881,c_5410,c_6149,c_6268,c_7367,c_17245])).

cnf(c_17275,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11621,c_17268])).

cnf(c_1901,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5408,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1901,c_1886])).

cnf(c_17830,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_17275,c_5408])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17830,c_7367,c_2487,c_2329,c_2211,c_43,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:35:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.62/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/0.98  
% 3.62/0.98  ------  iProver source info
% 3.62/0.98  
% 3.62/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.62/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/0.98  git: non_committed_changes: false
% 3.62/0.98  git: last_make_outside_of_git: false
% 3.62/0.98  
% 3.62/0.98  ------ 
% 3.62/0.98  
% 3.62/0.98  ------ Input Options
% 3.62/0.98  
% 3.62/0.98  --out_options                           all
% 3.62/0.98  --tptp_safe_out                         true
% 3.62/0.98  --problem_path                          ""
% 3.62/0.98  --include_path                          ""
% 3.62/0.98  --clausifier                            res/vclausify_rel
% 3.62/0.98  --clausifier_options                    --mode clausify
% 3.62/0.98  --stdin                                 false
% 3.62/0.98  --stats_out                             all
% 3.62/0.98  
% 3.62/0.98  ------ General Options
% 3.62/0.98  
% 3.62/0.98  --fof                                   false
% 3.62/0.98  --time_out_real                         305.
% 3.62/0.98  --time_out_virtual                      -1.
% 3.62/0.98  --symbol_type_check                     false
% 3.62/0.98  --clausify_out                          false
% 3.62/0.98  --sig_cnt_out                           false
% 3.62/0.98  --trig_cnt_out                          false
% 3.62/0.98  --trig_cnt_out_tolerance                1.
% 3.62/0.98  --trig_cnt_out_sk_spl                   false
% 3.62/0.98  --abstr_cl_out                          false
% 3.62/0.98  
% 3.62/0.98  ------ Global Options
% 3.62/0.98  
% 3.62/0.98  --schedule                              default
% 3.62/0.98  --add_important_lit                     false
% 3.62/0.98  --prop_solver_per_cl                    1000
% 3.62/0.98  --min_unsat_core                        false
% 3.62/0.98  --soft_assumptions                      false
% 3.62/0.98  --soft_lemma_size                       3
% 3.62/0.98  --prop_impl_unit_size                   0
% 3.62/0.98  --prop_impl_unit                        []
% 3.62/0.98  --share_sel_clauses                     true
% 3.62/0.98  --reset_solvers                         false
% 3.62/0.98  --bc_imp_inh                            [conj_cone]
% 3.62/0.98  --conj_cone_tolerance                   3.
% 3.62/0.98  --extra_neg_conj                        none
% 3.62/0.98  --large_theory_mode                     true
% 3.62/0.98  --prolific_symb_bound                   200
% 3.62/0.98  --lt_threshold                          2000
% 3.62/0.98  --clause_weak_htbl                      true
% 3.62/0.98  --gc_record_bc_elim                     false
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing Options
% 3.62/0.98  
% 3.62/0.98  --preprocessing_flag                    true
% 3.62/0.98  --time_out_prep_mult                    0.1
% 3.62/0.98  --splitting_mode                        input
% 3.62/0.98  --splitting_grd                         true
% 3.62/0.98  --splitting_cvd                         false
% 3.62/0.98  --splitting_cvd_svl                     false
% 3.62/0.98  --splitting_nvd                         32
% 3.62/0.98  --sub_typing                            true
% 3.62/0.98  --prep_gs_sim                           true
% 3.62/0.98  --prep_unflatten                        true
% 3.62/0.98  --prep_res_sim                          true
% 3.62/0.98  --prep_upred                            true
% 3.62/0.98  --prep_sem_filter                       exhaustive
% 3.62/0.98  --prep_sem_filter_out                   false
% 3.62/0.98  --pred_elim                             true
% 3.62/0.98  --res_sim_input                         true
% 3.62/0.98  --eq_ax_congr_red                       true
% 3.62/0.98  --pure_diseq_elim                       true
% 3.62/0.98  --brand_transform                       false
% 3.62/0.98  --non_eq_to_eq                          false
% 3.62/0.98  --prep_def_merge                        true
% 3.62/0.98  --prep_def_merge_prop_impl              false
% 3.62/0.98  --prep_def_merge_mbd                    true
% 3.62/0.98  --prep_def_merge_tr_red                 false
% 3.62/0.98  --prep_def_merge_tr_cl                  false
% 3.62/0.98  --smt_preprocessing                     true
% 3.62/0.98  --smt_ac_axioms                         fast
% 3.62/0.98  --preprocessed_out                      false
% 3.62/0.98  --preprocessed_stats                    false
% 3.62/0.98  
% 3.62/0.98  ------ Abstraction refinement Options
% 3.62/0.98  
% 3.62/0.98  --abstr_ref                             []
% 3.62/0.98  --abstr_ref_prep                        false
% 3.62/0.98  --abstr_ref_until_sat                   false
% 3.62/0.98  --abstr_ref_sig_restrict                funpre
% 3.62/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/0.98  --abstr_ref_under                       []
% 3.62/0.98  
% 3.62/0.98  ------ SAT Options
% 3.62/0.98  
% 3.62/0.98  --sat_mode                              false
% 3.62/0.98  --sat_fm_restart_options                ""
% 3.62/0.98  --sat_gr_def                            false
% 3.62/0.98  --sat_epr_types                         true
% 3.62/0.98  --sat_non_cyclic_types                  false
% 3.62/0.98  --sat_finite_models                     false
% 3.62/0.98  --sat_fm_lemmas                         false
% 3.62/0.98  --sat_fm_prep                           false
% 3.62/0.98  --sat_fm_uc_incr                        true
% 3.62/0.98  --sat_out_model                         small
% 3.62/0.98  --sat_out_clauses                       false
% 3.62/0.98  
% 3.62/0.98  ------ QBF Options
% 3.62/0.98  
% 3.62/0.98  --qbf_mode                              false
% 3.62/0.98  --qbf_elim_univ                         false
% 3.62/0.98  --qbf_dom_inst                          none
% 3.62/0.98  --qbf_dom_pre_inst                      false
% 3.62/0.98  --qbf_sk_in                             false
% 3.62/0.98  --qbf_pred_elim                         true
% 3.62/0.98  --qbf_split                             512
% 3.62/0.98  
% 3.62/0.98  ------ BMC1 Options
% 3.62/0.98  
% 3.62/0.98  --bmc1_incremental                      false
% 3.62/0.98  --bmc1_axioms                           reachable_all
% 3.62/0.98  --bmc1_min_bound                        0
% 3.62/0.98  --bmc1_max_bound                        -1
% 3.62/0.98  --bmc1_max_bound_default                -1
% 3.62/0.98  --bmc1_symbol_reachability              true
% 3.62/0.98  --bmc1_property_lemmas                  false
% 3.62/0.98  --bmc1_k_induction                      false
% 3.62/0.98  --bmc1_non_equiv_states                 false
% 3.62/0.98  --bmc1_deadlock                         false
% 3.62/0.98  --bmc1_ucm                              false
% 3.62/0.98  --bmc1_add_unsat_core                   none
% 3.62/0.98  --bmc1_unsat_core_children              false
% 3.62/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/0.98  --bmc1_out_stat                         full
% 3.62/0.98  --bmc1_ground_init                      false
% 3.62/0.98  --bmc1_pre_inst_next_state              false
% 3.62/0.98  --bmc1_pre_inst_state                   false
% 3.62/0.98  --bmc1_pre_inst_reach_state             false
% 3.62/0.98  --bmc1_out_unsat_core                   false
% 3.62/0.98  --bmc1_aig_witness_out                  false
% 3.62/0.98  --bmc1_verbose                          false
% 3.62/0.98  --bmc1_dump_clauses_tptp                false
% 3.62/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.62/0.98  --bmc1_dump_file                        -
% 3.62/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.62/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.62/0.98  --bmc1_ucm_extend_mode                  1
% 3.62/0.98  --bmc1_ucm_init_mode                    2
% 3.62/0.98  --bmc1_ucm_cone_mode                    none
% 3.62/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.62/0.98  --bmc1_ucm_relax_model                  4
% 3.62/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.62/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/0.98  --bmc1_ucm_layered_model                none
% 3.62/0.98  --bmc1_ucm_max_lemma_size               10
% 3.62/0.98  
% 3.62/0.98  ------ AIG Options
% 3.62/0.98  
% 3.62/0.98  --aig_mode                              false
% 3.62/0.98  
% 3.62/0.98  ------ Instantiation Options
% 3.62/0.98  
% 3.62/0.98  --instantiation_flag                    true
% 3.62/0.98  --inst_sos_flag                         false
% 3.62/0.98  --inst_sos_phase                        true
% 3.62/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/0.98  --inst_lit_sel_side                     num_symb
% 3.62/0.98  --inst_solver_per_active                1400
% 3.62/0.98  --inst_solver_calls_frac                1.
% 3.62/0.98  --inst_passive_queue_type               priority_queues
% 3.62/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/0.98  --inst_passive_queues_freq              [25;2]
% 3.62/0.98  --inst_dismatching                      true
% 3.62/0.98  --inst_eager_unprocessed_to_passive     true
% 3.62/0.98  --inst_prop_sim_given                   true
% 3.62/0.98  --inst_prop_sim_new                     false
% 3.62/0.98  --inst_subs_new                         false
% 3.62/0.98  --inst_eq_res_simp                      false
% 3.62/0.98  --inst_subs_given                       false
% 3.62/0.98  --inst_orphan_elimination               true
% 3.62/0.98  --inst_learning_loop_flag               true
% 3.62/0.98  --inst_learning_start                   3000
% 3.62/0.98  --inst_learning_factor                  2
% 3.62/0.98  --inst_start_prop_sim_after_learn       3
% 3.62/0.98  --inst_sel_renew                        solver
% 3.62/0.98  --inst_lit_activity_flag                true
% 3.62/0.98  --inst_restr_to_given                   false
% 3.62/0.98  --inst_activity_threshold               500
% 3.62/0.98  --inst_out_proof                        true
% 3.62/0.98  
% 3.62/0.98  ------ Resolution Options
% 3.62/0.98  
% 3.62/0.98  --resolution_flag                       true
% 3.62/0.98  --res_lit_sel                           adaptive
% 3.62/0.98  --res_lit_sel_side                      none
% 3.62/0.98  --res_ordering                          kbo
% 3.62/0.98  --res_to_prop_solver                    active
% 3.62/0.98  --res_prop_simpl_new                    false
% 3.62/0.98  --res_prop_simpl_given                  true
% 3.62/0.98  --res_passive_queue_type                priority_queues
% 3.62/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/0.98  --res_passive_queues_freq               [15;5]
% 3.62/0.98  --res_forward_subs                      full
% 3.62/0.98  --res_backward_subs                     full
% 3.62/0.98  --res_forward_subs_resolution           true
% 3.62/0.98  --res_backward_subs_resolution          true
% 3.62/0.98  --res_orphan_elimination                true
% 3.62/0.98  --res_time_limit                        2.
% 3.62/0.98  --res_out_proof                         true
% 3.62/0.98  
% 3.62/0.98  ------ Superposition Options
% 3.62/0.98  
% 3.62/0.98  --superposition_flag                    true
% 3.62/0.98  --sup_passive_queue_type                priority_queues
% 3.62/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.62/0.98  --demod_completeness_check              fast
% 3.62/0.98  --demod_use_ground                      true
% 3.62/0.98  --sup_to_prop_solver                    passive
% 3.62/0.98  --sup_prop_simpl_new                    true
% 3.62/0.98  --sup_prop_simpl_given                  true
% 3.62/0.98  --sup_fun_splitting                     false
% 3.62/0.98  --sup_smt_interval                      50000
% 3.62/0.98  
% 3.62/0.98  ------ Superposition Simplification Setup
% 3.62/0.98  
% 3.62/0.98  --sup_indices_passive                   []
% 3.62/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.98  --sup_full_bw                           [BwDemod]
% 3.62/0.98  --sup_immed_triv                        [TrivRules]
% 3.62/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.98  --sup_immed_bw_main                     []
% 3.62/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.98  
% 3.62/0.98  ------ Combination Options
% 3.62/0.98  
% 3.62/0.98  --comb_res_mult                         3
% 3.62/0.98  --comb_sup_mult                         2
% 3.62/0.98  --comb_inst_mult                        10
% 3.62/0.98  
% 3.62/0.98  ------ Debug Options
% 3.62/0.98  
% 3.62/0.98  --dbg_backtrace                         false
% 3.62/0.98  --dbg_dump_prop_clauses                 false
% 3.62/0.98  --dbg_dump_prop_clauses_file            -
% 3.62/0.98  --dbg_out_stat                          false
% 3.62/0.98  ------ Parsing...
% 3.62/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.98  ------ Proving...
% 3.62/0.98  ------ Problem Properties 
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  clauses                                 37
% 3.62/0.98  conjectures                             3
% 3.62/0.98  EPR                                     6
% 3.62/0.98  Horn                                    25
% 3.62/0.98  unary                                   6
% 3.62/0.98  binary                                  5
% 3.62/0.98  lits                                    99
% 3.62/0.98  lits eq                                 20
% 3.62/0.98  fd_pure                                 0
% 3.62/0.98  fd_pseudo                               0
% 3.62/0.98  fd_cond                                 3
% 3.62/0.98  fd_pseudo_cond                          1
% 3.62/0.98  AC symbols                              0
% 3.62/0.98  
% 3.62/0.98  ------ Schedule dynamic 5 is on 
% 3.62/0.98  
% 3.62/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  ------ 
% 3.62/0.98  Current options:
% 3.62/0.98  ------ 
% 3.62/0.98  
% 3.62/0.98  ------ Input Options
% 3.62/0.98  
% 3.62/0.98  --out_options                           all
% 3.62/0.98  --tptp_safe_out                         true
% 3.62/0.98  --problem_path                          ""
% 3.62/0.98  --include_path                          ""
% 3.62/0.98  --clausifier                            res/vclausify_rel
% 3.62/0.98  --clausifier_options                    --mode clausify
% 3.62/0.98  --stdin                                 false
% 3.62/0.98  --stats_out                             all
% 3.62/0.98  
% 3.62/0.98  ------ General Options
% 3.62/0.98  
% 3.62/0.98  --fof                                   false
% 3.62/0.98  --time_out_real                         305.
% 3.62/0.98  --time_out_virtual                      -1.
% 3.62/0.98  --symbol_type_check                     false
% 3.62/0.98  --clausify_out                          false
% 3.62/0.98  --sig_cnt_out                           false
% 3.62/0.98  --trig_cnt_out                          false
% 3.62/0.98  --trig_cnt_out_tolerance                1.
% 3.62/0.98  --trig_cnt_out_sk_spl                   false
% 3.62/0.98  --abstr_cl_out                          false
% 3.62/0.98  
% 3.62/0.98  ------ Global Options
% 3.62/0.98  
% 3.62/0.98  --schedule                              default
% 3.62/0.98  --add_important_lit                     false
% 3.62/0.98  --prop_solver_per_cl                    1000
% 3.62/0.98  --min_unsat_core                        false
% 3.62/0.98  --soft_assumptions                      false
% 3.62/0.98  --soft_lemma_size                       3
% 3.62/0.98  --prop_impl_unit_size                   0
% 3.62/0.98  --prop_impl_unit                        []
% 3.62/0.98  --share_sel_clauses                     true
% 3.62/0.98  --reset_solvers                         false
% 3.62/0.98  --bc_imp_inh                            [conj_cone]
% 3.62/0.98  --conj_cone_tolerance                   3.
% 3.62/0.98  --extra_neg_conj                        none
% 3.62/0.98  --large_theory_mode                     true
% 3.62/0.98  --prolific_symb_bound                   200
% 3.62/0.98  --lt_threshold                          2000
% 3.62/0.98  --clause_weak_htbl                      true
% 3.62/0.98  --gc_record_bc_elim                     false
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing Options
% 3.62/0.98  
% 3.62/0.98  --preprocessing_flag                    true
% 3.62/0.98  --time_out_prep_mult                    0.1
% 3.62/0.98  --splitting_mode                        input
% 3.62/0.98  --splitting_grd                         true
% 3.62/0.98  --splitting_cvd                         false
% 3.62/0.98  --splitting_cvd_svl                     false
% 3.62/0.98  --splitting_nvd                         32
% 3.62/0.98  --sub_typing                            true
% 3.62/0.98  --prep_gs_sim                           true
% 3.62/0.98  --prep_unflatten                        true
% 3.62/0.98  --prep_res_sim                          true
% 3.62/0.98  --prep_upred                            true
% 3.62/0.98  --prep_sem_filter                       exhaustive
% 3.62/0.98  --prep_sem_filter_out                   false
% 3.62/0.98  --pred_elim                             true
% 3.62/0.98  --res_sim_input                         true
% 3.62/0.98  --eq_ax_congr_red                       true
% 3.62/0.98  --pure_diseq_elim                       true
% 3.62/0.98  --brand_transform                       false
% 3.62/0.98  --non_eq_to_eq                          false
% 3.62/0.98  --prep_def_merge                        true
% 3.62/0.98  --prep_def_merge_prop_impl              false
% 3.62/0.98  --prep_def_merge_mbd                    true
% 3.62/0.98  --prep_def_merge_tr_red                 false
% 3.62/0.98  --prep_def_merge_tr_cl                  false
% 3.62/0.98  --smt_preprocessing                     true
% 3.62/0.98  --smt_ac_axioms                         fast
% 3.62/0.98  --preprocessed_out                      false
% 3.62/0.98  --preprocessed_stats                    false
% 3.62/0.98  
% 3.62/0.98  ------ Abstraction refinement Options
% 3.62/0.98  
% 3.62/0.98  --abstr_ref                             []
% 3.62/0.98  --abstr_ref_prep                        false
% 3.62/0.98  --abstr_ref_until_sat                   false
% 3.62/0.98  --abstr_ref_sig_restrict                funpre
% 3.62/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/0.98  --abstr_ref_under                       []
% 3.62/0.98  
% 3.62/0.98  ------ SAT Options
% 3.62/0.98  
% 3.62/0.98  --sat_mode                              false
% 3.62/0.98  --sat_fm_restart_options                ""
% 3.62/0.98  --sat_gr_def                            false
% 3.62/0.98  --sat_epr_types                         true
% 3.62/0.98  --sat_non_cyclic_types                  false
% 3.62/0.98  --sat_finite_models                     false
% 3.62/0.98  --sat_fm_lemmas                         false
% 3.62/0.98  --sat_fm_prep                           false
% 3.62/0.98  --sat_fm_uc_incr                        true
% 3.62/0.98  --sat_out_model                         small
% 3.62/0.98  --sat_out_clauses                       false
% 3.62/0.98  
% 3.62/0.98  ------ QBF Options
% 3.62/0.98  
% 3.62/0.98  --qbf_mode                              false
% 3.62/0.98  --qbf_elim_univ                         false
% 3.62/0.98  --qbf_dom_inst                          none
% 3.62/0.98  --qbf_dom_pre_inst                      false
% 3.62/0.98  --qbf_sk_in                             false
% 3.62/0.98  --qbf_pred_elim                         true
% 3.62/0.98  --qbf_split                             512
% 3.62/0.98  
% 3.62/0.98  ------ BMC1 Options
% 3.62/0.98  
% 3.62/0.98  --bmc1_incremental                      false
% 3.62/0.98  --bmc1_axioms                           reachable_all
% 3.62/0.98  --bmc1_min_bound                        0
% 3.62/0.98  --bmc1_max_bound                        -1
% 3.62/0.98  --bmc1_max_bound_default                -1
% 3.62/0.98  --bmc1_symbol_reachability              true
% 3.62/0.98  --bmc1_property_lemmas                  false
% 3.62/0.98  --bmc1_k_induction                      false
% 3.62/0.98  --bmc1_non_equiv_states                 false
% 3.62/0.98  --bmc1_deadlock                         false
% 3.62/0.98  --bmc1_ucm                              false
% 3.62/0.98  --bmc1_add_unsat_core                   none
% 3.62/0.98  --bmc1_unsat_core_children              false
% 3.62/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/0.98  --bmc1_out_stat                         full
% 3.62/0.98  --bmc1_ground_init                      false
% 3.62/0.98  --bmc1_pre_inst_next_state              false
% 3.62/0.98  --bmc1_pre_inst_state                   false
% 3.62/0.98  --bmc1_pre_inst_reach_state             false
% 3.62/0.98  --bmc1_out_unsat_core                   false
% 3.62/0.98  --bmc1_aig_witness_out                  false
% 3.62/0.98  --bmc1_verbose                          false
% 3.62/0.98  --bmc1_dump_clauses_tptp                false
% 3.62/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.62/0.98  --bmc1_dump_file                        -
% 3.62/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.62/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.62/0.98  --bmc1_ucm_extend_mode                  1
% 3.62/0.98  --bmc1_ucm_init_mode                    2
% 3.62/0.98  --bmc1_ucm_cone_mode                    none
% 3.62/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.62/0.98  --bmc1_ucm_relax_model                  4
% 3.62/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.62/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/0.98  --bmc1_ucm_layered_model                none
% 3.62/0.98  --bmc1_ucm_max_lemma_size               10
% 3.62/0.98  
% 3.62/0.98  ------ AIG Options
% 3.62/0.98  
% 3.62/0.98  --aig_mode                              false
% 3.62/0.98  
% 3.62/0.98  ------ Instantiation Options
% 3.62/0.98  
% 3.62/0.98  --instantiation_flag                    true
% 3.62/0.98  --inst_sos_flag                         false
% 3.62/0.98  --inst_sos_phase                        true
% 3.62/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/0.98  --inst_lit_sel_side                     none
% 3.62/0.98  --inst_solver_per_active                1400
% 3.62/0.98  --inst_solver_calls_frac                1.
% 3.62/0.98  --inst_passive_queue_type               priority_queues
% 3.62/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/0.98  --inst_passive_queues_freq              [25;2]
% 3.62/0.98  --inst_dismatching                      true
% 3.62/0.98  --inst_eager_unprocessed_to_passive     true
% 3.62/0.98  --inst_prop_sim_given                   true
% 3.62/0.98  --inst_prop_sim_new                     false
% 3.62/0.98  --inst_subs_new                         false
% 3.62/0.98  --inst_eq_res_simp                      false
% 3.62/0.98  --inst_subs_given                       false
% 3.62/0.98  --inst_orphan_elimination               true
% 3.62/0.98  --inst_learning_loop_flag               true
% 3.62/0.98  --inst_learning_start                   3000
% 3.62/0.98  --inst_learning_factor                  2
% 3.62/0.98  --inst_start_prop_sim_after_learn       3
% 3.62/0.98  --inst_sel_renew                        solver
% 3.62/0.98  --inst_lit_activity_flag                true
% 3.62/0.98  --inst_restr_to_given                   false
% 3.62/0.98  --inst_activity_threshold               500
% 3.62/0.98  --inst_out_proof                        true
% 3.62/0.98  
% 3.62/0.98  ------ Resolution Options
% 3.62/0.98  
% 3.62/0.98  --resolution_flag                       false
% 3.62/0.98  --res_lit_sel                           adaptive
% 3.62/0.98  --res_lit_sel_side                      none
% 3.62/0.98  --res_ordering                          kbo
% 3.62/0.98  --res_to_prop_solver                    active
% 3.62/0.98  --res_prop_simpl_new                    false
% 3.62/0.98  --res_prop_simpl_given                  true
% 3.62/0.98  --res_passive_queue_type                priority_queues
% 3.62/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/0.98  --res_passive_queues_freq               [15;5]
% 3.62/0.98  --res_forward_subs                      full
% 3.62/0.98  --res_backward_subs                     full
% 3.62/0.98  --res_forward_subs_resolution           true
% 3.62/0.98  --res_backward_subs_resolution          true
% 3.62/0.98  --res_orphan_elimination                true
% 3.62/0.98  --res_time_limit                        2.
% 3.62/0.98  --res_out_proof                         true
% 3.62/0.98  
% 3.62/0.98  ------ Superposition Options
% 3.62/0.98  
% 3.62/0.98  --superposition_flag                    true
% 3.62/0.98  --sup_passive_queue_type                priority_queues
% 3.62/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.62/0.98  --demod_completeness_check              fast
% 3.62/0.98  --demod_use_ground                      true
% 3.62/0.98  --sup_to_prop_solver                    passive
% 3.62/0.98  --sup_prop_simpl_new                    true
% 3.62/0.98  --sup_prop_simpl_given                  true
% 3.62/0.98  --sup_fun_splitting                     false
% 3.62/0.98  --sup_smt_interval                      50000
% 3.62/0.98  
% 3.62/0.98  ------ Superposition Simplification Setup
% 3.62/0.98  
% 3.62/0.98  --sup_indices_passive                   []
% 3.62/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.98  --sup_full_bw                           [BwDemod]
% 3.62/0.98  --sup_immed_triv                        [TrivRules]
% 3.62/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.98  --sup_immed_bw_main                     []
% 3.62/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.98  
% 3.62/0.98  ------ Combination Options
% 3.62/0.98  
% 3.62/0.98  --comb_res_mult                         3
% 3.62/0.98  --comb_sup_mult                         2
% 3.62/0.98  --comb_inst_mult                        10
% 3.62/0.98  
% 3.62/0.98  ------ Debug Options
% 3.62/0.98  
% 3.62/0.98  --dbg_backtrace                         false
% 3.62/0.98  --dbg_dump_prop_clauses                 false
% 3.62/0.98  --dbg_dump_prop_clauses_file            -
% 3.62/0.98  --dbg_out_stat                          false
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  ------ Proving...
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  % SZS status Theorem for theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  fof(f15,conjecture,(
% 3.62/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f16,negated_conjecture,(
% 3.62/0.98    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.62/0.98    inference(negated_conjecture,[],[f15])).
% 3.62/0.98  
% 3.62/0.98  fof(f32,plain,(
% 3.62/0.98    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.62/0.98    inference(ennf_transformation,[],[f16])).
% 3.62/0.98  
% 3.62/0.98  fof(f33,plain,(
% 3.62/0.98    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.62/0.98    inference(flattening,[],[f32])).
% 3.62/0.98  
% 3.62/0.98  fof(f43,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK4),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.62/0.98    introduced(choice_axiom,[])).
% 3.62/0.98  
% 3.62/0.98  fof(f42,plain,(
% 3.62/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK3,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) & v1_funct_2(X3,X1,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))) )),
% 3.62/0.98    introduced(choice_axiom,[])).
% 3.62/0.98  
% 3.62/0.98  fof(f41,plain,(
% 3.62/0.98    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK2,X2,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_2(X3,sK2,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))),
% 3.62/0.98    introduced(choice_axiom,[])).
% 3.62/0.98  
% 3.62/0.98  fof(f44,plain,(
% 3.62/0.98    ((~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 3.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f33,f43,f42,f41])).
% 3.62/0.98  
% 3.62/0.98  fof(f77,plain,(
% 3.62/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.62/0.98    inference(cnf_transformation,[],[f44])).
% 3.62/0.98  
% 3.62/0.98  fof(f12,axiom,(
% 3.62/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f26,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.98    inference(ennf_transformation,[],[f12])).
% 3.62/0.98  
% 3.62/0.98  fof(f27,plain,(
% 3.62/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.98    inference(flattening,[],[f26])).
% 3.62/0.98  
% 3.62/0.98  fof(f38,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.98    inference(nnf_transformation,[],[f27])).
% 3.62/0.98  
% 3.62/0.98  fof(f60,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f38])).
% 3.62/0.98  
% 3.62/0.98  fof(f10,axiom,(
% 3.62/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f24,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.98    inference(ennf_transformation,[],[f10])).
% 3.62/0.98  
% 3.62/0.98  fof(f58,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f24])).
% 3.62/0.98  
% 3.62/0.98  fof(f76,plain,(
% 3.62/0.98    v1_funct_2(sK4,sK2,sK3)),
% 3.62/0.98    inference(cnf_transformation,[],[f44])).
% 3.62/0.98  
% 3.62/0.98  fof(f4,axiom,(
% 3.62/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f20,plain,(
% 3.62/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.62/0.98    inference(ennf_transformation,[],[f4])).
% 3.62/0.98  
% 3.62/0.98  fof(f50,plain,(
% 3.62/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f20])).
% 3.62/0.98  
% 3.62/0.98  fof(f14,axiom,(
% 3.62/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f30,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.62/0.98    inference(ennf_transformation,[],[f14])).
% 3.62/0.98  
% 3.62/0.98  fof(f31,plain,(
% 3.62/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.62/0.98    inference(flattening,[],[f30])).
% 3.62/0.98  
% 3.62/0.98  fof(f39,plain,(
% 3.62/0.98    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 3.62/0.98    introduced(choice_axiom,[])).
% 3.62/0.98  
% 3.62/0.98  fof(f40,plain,(
% 3.62/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f39])).
% 3.62/0.98  
% 3.62/0.98  fof(f71,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f40])).
% 3.62/0.98  
% 3.62/0.98  fof(f88,plain,(
% 3.62/0.98    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.62/0.98    inference(equality_resolution,[],[f71])).
% 3.62/0.98  
% 3.62/0.98  fof(f75,plain,(
% 3.62/0.98    v1_funct_1(sK4)),
% 3.62/0.98    inference(cnf_transformation,[],[f44])).
% 3.62/0.98  
% 3.62/0.98  fof(f79,plain,(
% 3.62/0.98    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)),
% 3.62/0.98    inference(cnf_transformation,[],[f44])).
% 3.62/0.98  
% 3.62/0.98  fof(f3,axiom,(
% 3.62/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f49,plain,(
% 3.62/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f3])).
% 3.62/0.98  
% 3.62/0.98  fof(f1,axiom,(
% 3.62/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f34,plain,(
% 3.62/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.62/0.98    inference(nnf_transformation,[],[f1])).
% 3.62/0.98  
% 3.62/0.98  fof(f35,plain,(
% 3.62/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.62/0.98    inference(flattening,[],[f34])).
% 3.62/0.98  
% 3.62/0.98  fof(f47,plain,(
% 3.62/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f35])).
% 3.62/0.98  
% 3.62/0.98  fof(f11,axiom,(
% 3.62/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f25,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.98    inference(ennf_transformation,[],[f11])).
% 3.62/0.98  
% 3.62/0.98  fof(f59,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f25])).
% 3.62/0.98  
% 3.62/0.98  fof(f2,axiom,(
% 3.62/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f18,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.62/0.98    inference(ennf_transformation,[],[f2])).
% 3.62/0.98  
% 3.62/0.98  fof(f19,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.62/0.98    inference(flattening,[],[f18])).
% 3.62/0.98  
% 3.62/0.98  fof(f48,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f19])).
% 3.62/0.98  
% 3.62/0.98  fof(f9,axiom,(
% 3.62/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f17,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.62/0.98    inference(pure_predicate_removal,[],[f9])).
% 3.62/0.98  
% 3.62/0.98  fof(f23,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.98    inference(ennf_transformation,[],[f17])).
% 3.62/0.98  
% 3.62/0.98  fof(f57,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f23])).
% 3.62/0.98  
% 3.62/0.98  fof(f7,axiom,(
% 3.62/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f22,plain,(
% 3.62/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.62/0.98    inference(ennf_transformation,[],[f7])).
% 3.62/0.98  
% 3.62/0.98  fof(f37,plain,(
% 3.62/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.62/0.98    inference(nnf_transformation,[],[f22])).
% 3.62/0.98  
% 3.62/0.98  fof(f54,plain,(
% 3.62/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f37])).
% 3.62/0.98  
% 3.62/0.98  fof(f5,axiom,(
% 3.62/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f36,plain,(
% 3.62/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.62/0.98    inference(nnf_transformation,[],[f5])).
% 3.62/0.98  
% 3.62/0.98  fof(f51,plain,(
% 3.62/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f36])).
% 3.62/0.98  
% 3.62/0.98  fof(f6,axiom,(
% 3.62/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f21,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.62/0.98    inference(ennf_transformation,[],[f6])).
% 3.62/0.98  
% 3.62/0.98  fof(f53,plain,(
% 3.62/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f21])).
% 3.62/0.98  
% 3.62/0.98  fof(f52,plain,(
% 3.62/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f36])).
% 3.62/0.98  
% 3.62/0.98  fof(f8,axiom,(
% 3.62/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f56,plain,(
% 3.62/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f8])).
% 3.62/0.98  
% 3.62/0.98  fof(f13,axiom,(
% 3.62/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f28,plain,(
% 3.62/0.98    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.62/0.98    inference(ennf_transformation,[],[f13])).
% 3.62/0.98  
% 3.62/0.98  fof(f29,plain,(
% 3.62/0.98    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.62/0.98    inference(flattening,[],[f28])).
% 3.62/0.98  
% 3.62/0.98  fof(f66,plain,(
% 3.62/0.98    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f29])).
% 3.62/0.98  
% 3.62/0.98  fof(f73,plain,(
% 3.62/0.98    ~v1_xboole_0(sK2)),
% 3.62/0.98    inference(cnf_transformation,[],[f44])).
% 3.62/0.98  
% 3.62/0.98  fof(f78,plain,(
% 3.62/0.98    ( ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f44])).
% 3.62/0.98  
% 3.62/0.98  fof(f72,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f40])).
% 3.62/0.98  
% 3.62/0.98  fof(f87,plain,(
% 3.62/0.98    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.62/0.98    inference(equality_resolution,[],[f72])).
% 3.62/0.98  
% 3.62/0.98  fof(f70,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f40])).
% 3.62/0.98  
% 3.62/0.98  fof(f89,plain,(
% 3.62/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.62/0.98    inference(equality_resolution,[],[f70])).
% 3.62/0.98  
% 3.62/0.98  cnf(c_30,negated_conjecture,
% 3.62/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.62/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1889,plain,
% 3.62/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_20,plain,
% 3.62/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.62/0.98      | k1_xboole_0 = X2 ),
% 3.62/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1891,plain,
% 3.62/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.62/0.98      | k1_xboole_0 = X1
% 3.62/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.62/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_5780,plain,
% 3.62/0.98      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 3.62/0.98      | sK3 = k1_xboole_0
% 3.62/0.98      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_1889,c_1891]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_13,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1898,plain,
% 3.62/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.62/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3199,plain,
% 3.62/0.98      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_1889,c_1898]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_5802,plain,
% 3.62/0.98      ( k1_relat_1(sK4) = sK2
% 3.62/0.98      | sK3 = k1_xboole_0
% 3.62/0.98      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.62/0.98      inference(demodulation,[status(thm)],[c_5780,c_3199]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_31,negated_conjecture,
% 3.62/0.98      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.62/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_38,plain,
% 3.62/0.98      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_6399,plain,
% 3.62/0.98      ( sK3 = k1_xboole_0 | k1_relat_1(sK4) = sK2 ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_5802,c_38]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_6400,plain,
% 3.62/0.98      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.62/0.98      inference(renaming,[status(thm)],[c_6399]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_5,plain,
% 3.62/0.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.62/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_23,plain,
% 3.62/0.98      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.62/0.98      | ~ v1_funct_1(X0)
% 3.62/0.98      | ~ v1_relat_1(X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_32,negated_conjecture,
% 3.62/0.98      ( v1_funct_1(sK4) ),
% 3.62/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_573,plain,
% 3.62/0.98      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.62/0.98      | ~ v1_relat_1(X0)
% 3.62/0.98      | sK4 != X0 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_574,plain,
% 3.62/0.98      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 3.62/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.62/0.98      | ~ v1_relat_1(sK4) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_573]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_641,plain,
% 3.62/0.98      ( m1_subset_1(X0,X1)
% 3.62/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X2)))
% 3.62/0.98      | ~ v1_relat_1(sK4)
% 3.62/0.98      | sK0(k1_relat_1(sK4),X2,sK4) != X0
% 3.62/0.98      | k1_relat_1(sK4) != X1 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_574]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_642,plain,
% 3.62/0.98      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 3.62/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.62/0.98      | ~ v1_relat_1(sK4) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_641]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1882,plain,
% 3.62/0.98      ( m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 3.62/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.62/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_6407,plain,
% 3.62/0.98      ( sK3 = k1_xboole_0
% 3.62/0.98      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.62/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_6400,c_1882]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_28,negated_conjecture,
% 3.62/0.98      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
% 3.62/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_43,plain,
% 3.62/0.98      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4,plain,
% 3.62/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_108,plain,
% 3.62/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_107,plain,
% 3.62/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_109,plain,
% 3.62/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_107]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_0,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.62/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_114,plain,
% 3.62/0.98      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.62/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_14,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2211,plain,
% 3.62/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.62/0.98      | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2265,plain,
% 3.62/0.98      ( r1_tarski(k1_xboole_0,sK1) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2268,plain,
% 3.62/0.98      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_2265]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1099,plain,( X0 = X0 ),theory(equality) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2329,plain,
% 3.62/0.98      ( sK1 = sK1 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_1099]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1101,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.62/0.98      theory(equality) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2214,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,X1)
% 3.62/0.98      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 3.62/0.98      | k2_relset_1(sK2,sK3,sK4) != X0
% 3.62/0.98      | sK1 != X1 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_1101]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2328,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,sK1)
% 3.62/0.98      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 3.62/0.98      | k2_relset_1(sK2,sK3,sK4) != X0
% 3.62/0.98      | sK1 != sK1 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_2214]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2486,plain,
% 3.62/0.98      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
% 3.62/0.98      | ~ r1_tarski(k2_relat_1(sK4),sK1)
% 3.62/0.98      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.62/0.98      | sK1 != sK1 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_2328]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2487,plain,
% 3.62/0.98      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.62/0.98      | sK1 != sK1
% 3.62/0.98      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) = iProver_top
% 3.62/0.98      | r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_2486]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.62/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2261,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK1) | r1_tarski(X0,sK1) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2875,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,sK1)
% 3.62/0.98      | ~ r1_tarski(k2_relat_1(sK4),X0)
% 3.62/0.98      | r1_tarski(k2_relat_1(sK4),sK1) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_2261]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2879,plain,
% 3.62/0.98      ( r1_tarski(X0,sK1) != iProver_top
% 3.62/0.98      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 3.62/0.98      | r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_2875]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2881,plain,
% 3.62/0.98      ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
% 3.62/0.98      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.62/0.98      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_2879]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_12,plain,
% 3.62/0.98      ( v5_relat_1(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.62/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_10,plain,
% 3.62/0.98      ( ~ v5_relat_1(X0,X1)
% 3.62/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 3.62/0.98      | ~ v1_relat_1(X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_434,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 3.62/0.98      | ~ v1_relat_1(X0) ),
% 3.62/0.98      inference(resolution,[status(thm)],[c_12,c_10]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1886,plain,
% 3.62/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.62/0.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.62/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_5409,plain,
% 3.62/0.98      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
% 3.62/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_1889,c_1886]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1903,plain,
% 3.62/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.62/0.98      | r1_tarski(X1,X2) != iProver_top
% 3.62/0.98      | r1_tarski(X0,X2) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_6134,plain,
% 3.62/0.98      ( r1_tarski(k2_relat_1(sK4),X0) = iProver_top
% 3.62/0.98      | r1_tarski(sK3,X0) != iProver_top
% 3.62/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_5409,c_1903]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_6149,plain,
% 3.62/0.98      ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top
% 3.62/0.98      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.62/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_6134]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_6265,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,X1)
% 3.62/0.98      | r1_tarski(sK3,k1_xboole_0)
% 3.62/0.98      | sK3 != X0
% 3.62/0.98      | k1_xboole_0 != X1 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_1101]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_6266,plain,
% 3.62/0.98      ( sK3 != X0
% 3.62/0.98      | k1_xboole_0 != X1
% 3.62/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.62/0.98      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_6265]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_6268,plain,
% 3.62/0.98      ( sK3 != k1_xboole_0
% 3.62/0.98      | k1_xboole_0 != k1_xboole_0
% 3.62/0.98      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 3.62/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_6266]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.62/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1900,plain,
% 3.62/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.62/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2525,plain,
% 3.62/0.98      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_1889,c_1900]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_8,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/0.98      | ~ v1_relat_1(X1)
% 3.62/0.98      | v1_relat_1(X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_6,plain,
% 3.62/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.62/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_260,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.62/0.98      inference(prop_impl,[status(thm)],[c_6]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_261,plain,
% 3.62/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.62/0.98      inference(renaming,[status(thm)],[c_260]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_320,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.62/0.98      inference(bin_hyper_res,[status(thm)],[c_8,c_261]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1887,plain,
% 3.62/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.62/0.98      | v1_relat_1(X1) != iProver_top
% 3.62/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7071,plain,
% 3.62/0.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 3.62/0.98      | v1_relat_1(sK4) = iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_2525,c_1887]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_11,plain,
% 3.62/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.62/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1899,plain,
% 3.62/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7367,plain,
% 3.62/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 3.62/0.98      inference(forward_subsumption_resolution,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_7071,c_1899]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_11612,plain,
% 3.62/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.62/0.98      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_6407,c_30,c_43,c_108,c_109,c_114,c_2211,c_2268,c_2329,
% 3.62/0.98                 c_2487,c_2881,c_6149,c_6268,c_7367]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_11613,plain,
% 3.62/0.98      ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 3.62/0.98      inference(renaming,[status(thm)],[c_11612]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_11621,plain,
% 3.62/0.98      ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.62/0.98      | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),X0)) = iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_11613,c_1900]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_11620,plain,
% 3.62/0.98      ( sK3 = k1_xboole_0
% 3.62/0.98      | m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_6400,c_11613]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_11676,plain,
% 3.62/0.98      ( m1_subset_1(sK0(sK2,X0,sK4),sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_11620,c_30,c_43,c_108,c_109,c_114,c_2211,c_2268,
% 3.62/0.98                 c_2329,c_2487,c_2881,c_6149,c_6268,c_7367]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_21,plain,
% 3.62/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.62/0.98      | ~ m1_subset_1(X3,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.98      | v1_xboole_0(X1)
% 3.62/0.98      | ~ v1_funct_1(X0)
% 3.62/0.98      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.62/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_34,negated_conjecture,
% 3.62/0.98      ( ~ v1_xboole_0(sK2) ),
% 3.62/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_474,plain,
% 3.62/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.62/0.98      | ~ m1_subset_1(X3,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.98      | ~ v1_funct_1(X0)
% 3.62/0.98      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 3.62/0.98      | sK2 != X1 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_34]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_475,plain,
% 3.62/0.98      ( ~ v1_funct_2(X0,sK2,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 3.62/0.98      | ~ m1_subset_1(X2,sK2)
% 3.62/0.98      | ~ v1_funct_1(X0)
% 3.62/0.98      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_474]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_507,plain,
% 3.62/0.98      ( ~ v1_funct_2(X0,sK2,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 3.62/0.98      | ~ m1_subset_1(X2,sK2)
% 3.62/0.98      | k3_funct_2(sK2,X1,X0,X2) = k1_funct_1(X0,X2)
% 3.62/0.98      | sK4 != X0 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_475,c_32]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_508,plain,
% 3.62/0.98      ( ~ v1_funct_2(sK4,sK2,X0)
% 3.62/0.98      | ~ m1_subset_1(X1,sK2)
% 3.62/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 3.62/0.98      | k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_507]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1885,plain,
% 3.62/0.98      ( k3_funct_2(sK2,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 3.62/0.98      | v1_funct_2(sK4,sK2,X0) != iProver_top
% 3.62/0.98      | m1_subset_1(X1,sK2) != iProver_top
% 3.62/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2230,plain,
% 3.62/0.98      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 3.62/0.98      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.62/0.98      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_1889,c_1885]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2235,plain,
% 3.62/0.98      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 3.62/0.98      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_2230,c_38]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_11684,plain,
% 3.62/0.98      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.62/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_11676,c_2235]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_12118,plain,
% 3.62/0.98      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.62/0.98      | r1_tarski(k2_relat_1(sK4),X0) = iProver_top
% 3.62/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_11684,c_1886]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_15646,plain,
% 3.62/0.98      ( r1_tarski(k2_relat_1(sK4),X0) = iProver_top
% 3.62/0.98      | k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4)) ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_12118,c_7367]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_15647,plain,
% 3.62/0.98      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,X0,sK4)) = k1_funct_1(sK4,sK0(sK2,X0,sK4))
% 3.62/0.98      | r1_tarski(k2_relat_1(sK4),X0) = iProver_top ),
% 3.62/0.98      inference(renaming,[status(thm)],[c_15646]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1897,plain,
% 3.62/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.62/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3003,plain,
% 3.62/0.98      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_1889,c_1897]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1890,plain,
% 3.62/0.98      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3374,plain,
% 3.62/0.98      ( r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
% 3.62/0.98      inference(demodulation,[status(thm)],[c_3003,c_1890]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_15660,plain,
% 3.62/0.98      ( k3_funct_2(sK2,sK3,sK4,sK0(sK2,sK1,sK4)) = k1_funct_1(sK4,sK0(sK2,sK1,sK4)) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_15647,c_3374]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_29,negated_conjecture,
% 3.62/0.98      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
% 3.62/0.98      | ~ m1_subset_1(X0,sK2) ),
% 3.62/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_629,plain,
% 3.62/0.98      ( m1_subset_1(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X2,sK2)
% 3.62/0.98      | k3_funct_2(sK2,sK3,sK4,X2) != X0
% 3.62/0.98      | sK1 != X1 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_29]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_630,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,sK2)
% 3.62/0.98      | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_629]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1883,plain,
% 3.62/0.98      ( m1_subset_1(X0,sK2) != iProver_top
% 3.62/0.98      | m1_subset_1(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_17247,plain,
% 3.62/0.98      ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 3.62/0.98      | m1_subset_1(k1_funct_1(sK4,sK0(sK2,sK1,sK4)),sK1) = iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_15660,c_1883]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_22,plain,
% 3.62/0.98      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.62/0.98      | ~ v1_funct_1(X0)
% 3.62/0.98      | ~ v1_relat_1(X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_588,plain,
% 3.62/0.98      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.62/0.98      | ~ v1_relat_1(X0)
% 3.62/0.98      | sK4 != X0 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_589,plain,
% 3.62/0.98      ( ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 3.62/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.62/0.98      | ~ v1_relat_1(sK4) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_588]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_671,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,sK2)
% 3.62/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X1)))
% 3.62/0.98      | ~ v1_relat_1(sK4)
% 3.62/0.98      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 3.62/0.98      | sK1 != X1 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_589]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_672,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,sK2)
% 3.62/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 3.62/0.98      | ~ v1_relat_1(sK4)
% 3.62/0.98      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_671]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1097,plain,
% 3.62/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))
% 3.62/0.98      | ~ v1_relat_1(sK4)
% 3.62/0.98      | sP2_iProver_split ),
% 3.62/0.98      inference(splitting,
% 3.62/0.98                [splitting(split),new_symbols(definition,[])],
% 3.62/0.98                [c_672]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1879,plain,
% 3.62/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 3.62/0.98      | v1_relat_1(sK4) != iProver_top
% 3.62/0.98      | sP2_iProver_split = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_1097]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_5410,plain,
% 3.62/0.98      ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
% 3.62/0.98      | v1_relat_1(sK4) != iProver_top
% 3.62/0.98      | sP2_iProver_split = iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_1879,c_1886]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_24,plain,
% 3.62/0.98      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.62/0.98      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.62/0.98      | ~ v1_funct_1(X0)
% 3.62/0.98      | ~ v1_relat_1(X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_558,plain,
% 3.62/0.98      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.62/0.98      | ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 3.62/0.98      | ~ v1_relat_1(X0)
% 3.62/0.98      | sK4 != X0 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_559,plain,
% 3.62/0.98      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 3.62/0.98      | ~ r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),X0)
% 3.62/0.98      | ~ v1_relat_1(sK4) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_558]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_689,plain,
% 3.62/0.98      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 3.62/0.98      | ~ m1_subset_1(X1,sK2)
% 3.62/0.98      | ~ v1_relat_1(sK4)
% 3.62/0.98      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)) != k3_funct_2(sK2,sK3,sK4,X1)
% 3.62/0.98      | sK1 != X0 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_559]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_690,plain,
% 3.62/0.98      ( v1_funct_2(sK4,k1_relat_1(sK4),sK1)
% 3.62/0.98      | ~ m1_subset_1(X0,sK2)
% 3.62/0.98      | ~ v1_relat_1(sK4)
% 3.62/0.98      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_689]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1095,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,sK2)
% 3.62/0.98      | k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 3.62/0.98      | ~ sP2_iProver_split ),
% 3.62/0.98      inference(splitting,
% 3.62/0.98                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.62/0.98                [c_690]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1878,plain,
% 3.62/0.98      ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 3.62/0.98      | m1_subset_1(X0,sK2) != iProver_top
% 3.62/0.98      | sP2_iProver_split != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_1095]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_6428,plain,
% 3.62/0.98      ( k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != k3_funct_2(sK2,sK3,sK4,X0)
% 3.62/0.98      | sK3 = k1_xboole_0
% 3.62/0.98      | m1_subset_1(X0,sK2) != iProver_top
% 3.62/0.98      | sP2_iProver_split != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_6400,c_1878]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_17245,plain,
% 3.62/0.98      ( sK3 = k1_xboole_0
% 3.62/0.98      | m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top
% 3.62/0.98      | sP2_iProver_split != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_15660,c_6428]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_17268,plain,
% 3.62/0.98      ( m1_subset_1(sK0(sK2,sK1,sK4),sK2) != iProver_top ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_17247,c_30,c_43,c_108,c_109,c_114,c_2211,c_2268,
% 3.62/0.98                 c_2329,c_2487,c_2881,c_5410,c_6149,c_6268,c_7367,
% 3.62/0.98                 c_17245]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_17275,plain,
% 3.62/0.98      ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) = iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_11621,c_17268]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1901,plain,
% 3.62/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.62/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_5408,plain,
% 3.62/0.98      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.62/0.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.62/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_1901,c_1886]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_17830,plain,
% 3.62/0.98      ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
% 3.62/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_17275,c_5408]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(contradiction,plain,
% 3.62/0.98      ( $false ),
% 3.62/0.98      inference(minisat,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_17830,c_7367,c_2487,c_2329,c_2211,c_43,c_30]) ).
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  ------                               Statistics
% 3.62/0.98  
% 3.62/0.98  ------ General
% 3.62/0.98  
% 3.62/0.98  abstr_ref_over_cycles:                  0
% 3.62/0.98  abstr_ref_under_cycles:                 0
% 3.62/0.98  gc_basic_clause_elim:                   0
% 3.62/0.98  forced_gc_time:                         0
% 3.62/0.98  parsing_time:                           0.009
% 3.62/0.98  unif_index_cands_time:                  0.
% 3.62/0.98  unif_index_add_time:                    0.
% 3.62/0.98  orderings_time:                         0.
% 3.62/0.98  out_proof_time:                         0.014
% 3.62/0.98  total_time:                             0.389
% 3.62/0.98  num_of_symbols:                         56
% 3.62/0.98  num_of_terms:                           9423
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing
% 3.62/0.98  
% 3.62/0.98  num_of_splits:                          6
% 3.62/0.98  num_of_split_atoms:                     3
% 3.62/0.98  num_of_reused_defs:                     3
% 3.62/0.98  num_eq_ax_congr_red:                    18
% 3.62/0.98  num_of_sem_filtered_clauses:            1
% 3.62/0.98  num_of_subtypes:                        0
% 3.62/0.98  monotx_restored_types:                  0
% 3.62/0.98  sat_num_of_epr_types:                   0
% 3.62/0.98  sat_num_of_non_cyclic_types:            0
% 3.62/0.98  sat_guarded_non_collapsed_types:        0
% 3.62/0.98  num_pure_diseq_elim:                    0
% 3.62/0.98  simp_replaced_by:                       0
% 3.62/0.98  res_preprocessed:                       160
% 3.62/0.98  prep_upred:                             0
% 3.62/0.98  prep_unflattend:                        20
% 3.62/0.98  smt_new_axioms:                         0
% 3.62/0.98  pred_elim_cands:                        4
% 3.62/0.98  pred_elim:                              4
% 3.62/0.98  pred_elim_cl:                           1
% 3.62/0.98  pred_elim_cycles:                       6
% 3.62/0.98  merged_defs:                            8
% 3.62/0.98  merged_defs_ncl:                        0
% 3.62/0.98  bin_hyper_res:                          9
% 3.62/0.98  prep_cycles:                            4
% 3.62/0.98  pred_elim_time:                         0.009
% 3.62/0.98  splitting_time:                         0.
% 3.62/0.98  sem_filter_time:                        0.
% 3.62/0.98  monotx_time:                            0.
% 3.62/0.98  subtype_inf_time:                       0.
% 3.62/0.98  
% 3.62/0.98  ------ Problem properties
% 3.62/0.98  
% 3.62/0.98  clauses:                                37
% 3.62/0.98  conjectures:                            3
% 3.62/0.98  epr:                                    6
% 3.62/0.98  horn:                                   25
% 3.62/0.98  ground:                                 9
% 3.62/0.98  unary:                                  6
% 3.62/0.98  binary:                                 5
% 3.62/0.98  lits:                                   99
% 3.62/0.98  lits_eq:                                20
% 3.62/0.98  fd_pure:                                0
% 3.62/0.98  fd_pseudo:                              0
% 3.62/0.98  fd_cond:                                3
% 3.62/0.98  fd_pseudo_cond:                         1
% 3.62/0.98  ac_symbols:                             0
% 3.62/0.98  
% 3.62/0.98  ------ Propositional Solver
% 3.62/0.98  
% 3.62/0.98  prop_solver_calls:                      28
% 3.62/0.98  prop_fast_solver_calls:                 1495
% 3.62/0.98  smt_solver_calls:                       0
% 3.62/0.98  smt_fast_solver_calls:                  0
% 3.62/0.98  prop_num_of_clauses:                    5620
% 3.62/0.98  prop_preprocess_simplified:             13729
% 3.62/0.98  prop_fo_subsumed:                       66
% 3.62/0.98  prop_solver_time:                       0.
% 3.62/0.98  smt_solver_time:                        0.
% 3.62/0.98  smt_fast_solver_time:                   0.
% 3.62/0.98  prop_fast_solver_time:                  0.
% 3.62/0.98  prop_unsat_core_time:                   0.
% 3.62/0.98  
% 3.62/0.98  ------ QBF
% 3.62/0.98  
% 3.62/0.98  qbf_q_res:                              0
% 3.62/0.98  qbf_num_tautologies:                    0
% 3.62/0.98  qbf_prep_cycles:                        0
% 3.62/0.98  
% 3.62/0.98  ------ BMC1
% 3.62/0.98  
% 3.62/0.98  bmc1_current_bound:                     -1
% 3.62/0.98  bmc1_last_solved_bound:                 -1
% 3.62/0.98  bmc1_unsat_core_size:                   -1
% 3.62/0.98  bmc1_unsat_core_parents_size:           -1
% 3.62/0.98  bmc1_merge_next_fun:                    0
% 3.62/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.62/0.98  
% 3.62/0.98  ------ Instantiation
% 3.62/0.98  
% 3.62/0.98  inst_num_of_clauses:                    1576
% 3.62/0.98  inst_num_in_passive:                    128
% 3.62/0.98  inst_num_in_active:                     716
% 3.62/0.98  inst_num_in_unprocessed:                733
% 3.62/0.98  inst_num_of_loops:                      780
% 3.62/0.98  inst_num_of_learning_restarts:          0
% 3.62/0.98  inst_num_moves_active_passive:          62
% 3.62/0.98  inst_lit_activity:                      0
% 3.62/0.98  inst_lit_activity_moves:                0
% 3.62/0.98  inst_num_tautologies:                   0
% 3.62/0.98  inst_num_prop_implied:                  0
% 3.62/0.98  inst_num_existing_simplified:           0
% 3.62/0.98  inst_num_eq_res_simplified:             0
% 3.62/0.98  inst_num_child_elim:                    0
% 3.62/0.98  inst_num_of_dismatching_blockings:      948
% 3.62/0.98  inst_num_of_non_proper_insts:           2601
% 3.62/0.98  inst_num_of_duplicates:                 0
% 3.62/0.98  inst_inst_num_from_inst_to_res:         0
% 3.62/0.98  inst_dismatching_checking_time:         0.
% 3.62/0.98  
% 3.62/0.98  ------ Resolution
% 3.62/0.98  
% 3.62/0.98  res_num_of_clauses:                     0
% 3.62/0.98  res_num_in_passive:                     0
% 3.62/0.98  res_num_in_active:                      0
% 3.62/0.98  res_num_of_loops:                       164
% 3.62/0.98  res_forward_subset_subsumed:            183
% 3.62/0.98  res_backward_subset_subsumed:           4
% 3.62/0.98  res_forward_subsumed:                   0
% 3.62/0.98  res_backward_subsumed:                  0
% 3.62/0.98  res_forward_subsumption_resolution:     0
% 3.62/0.98  res_backward_subsumption_resolution:    0
% 3.62/0.98  res_clause_to_clause_subsumption:       899
% 3.62/0.98  res_orphan_elimination:                 0
% 3.62/0.98  res_tautology_del:                      299
% 3.62/0.98  res_num_eq_res_simplified:              0
% 3.62/0.98  res_num_sel_changes:                    0
% 3.62/0.98  res_moves_from_active_to_pass:          0
% 3.62/0.98  
% 3.62/0.98  ------ Superposition
% 3.62/0.98  
% 3.62/0.98  sup_time_total:                         0.
% 3.62/0.98  sup_time_generating:                    0.
% 3.62/0.98  sup_time_sim_full:                      0.
% 3.62/0.98  sup_time_sim_immed:                     0.
% 3.62/0.98  
% 3.62/0.98  sup_num_of_clauses:                     301
% 3.62/0.98  sup_num_in_active:                      146
% 3.62/0.98  sup_num_in_passive:                     155
% 3.62/0.98  sup_num_of_loops:                       155
% 3.62/0.98  sup_fw_superposition:                   165
% 3.62/0.98  sup_bw_superposition:                   249
% 3.62/0.98  sup_immediate_simplified:               48
% 3.62/0.98  sup_given_eliminated:                   1
% 3.62/0.98  comparisons_done:                       0
% 3.62/0.98  comparisons_avoided:                    18
% 3.62/0.98  
% 3.62/0.98  ------ Simplifications
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  sim_fw_subset_subsumed:                 18
% 3.62/0.98  sim_bw_subset_subsumed:                 14
% 3.62/0.98  sim_fw_subsumed:                        21
% 3.62/0.98  sim_bw_subsumed:                        3
% 3.62/0.98  sim_fw_subsumption_res:                 3
% 3.62/0.98  sim_bw_subsumption_res:                 0
% 3.62/0.98  sim_tautology_del:                      6
% 3.62/0.98  sim_eq_tautology_del:                   9
% 3.62/0.98  sim_eq_res_simp:                        0
% 3.62/0.98  sim_fw_demodulated:                     3
% 3.62/0.98  sim_bw_demodulated:                     9
% 3.62/0.98  sim_light_normalised:                   0
% 3.62/0.98  sim_joinable_taut:                      0
% 3.62/0.98  sim_joinable_simp:                      0
% 3.62/0.98  sim_ac_normalised:                      0
% 3.62/0.98  sim_smt_subsumption:                    0
% 3.62/0.98  
%------------------------------------------------------------------------------
