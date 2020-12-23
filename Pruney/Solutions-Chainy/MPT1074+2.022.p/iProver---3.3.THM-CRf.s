%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:16 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  163 (2339 expanded)
%              Number of clauses        :   97 ( 744 expanded)
%              Number of leaves         :   19 ( 621 expanded)
%              Depth                    :   30
%              Number of atoms          :  516 (13765 expanded)
%              Number of equality atoms :  172 (1720 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f26])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1)
        & r2_hidden(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1)
        & r2_hidden(sK1(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f36])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK1(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK1(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f65])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
              | ~ m1_subset_1(X4,X1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ~ r1_tarski(k2_relset_1(X1,X2,sK5),X0)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(X1,X2,sK5,X4),X0)
            | ~ m1_subset_1(X4,X1) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
            ( ~ r1_tarski(k2_relset_1(X1,sK4,X3),X0)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(X1,sK4,X3,X4),X0)
                | ~ m1_subset_1(X4,X1) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK4)))
            & v1_funct_2(X3,X1,sK4)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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
              ( ~ r1_tarski(k2_relset_1(sK3,X2,X3),sK2)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK3,X2,X3,X4),sK2)
                  | ~ m1_subset_1(X4,sK3) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X2)))
              & v1_funct_2(X3,sK3,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2)
        | ~ m1_subset_1(X4,sK3) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f40,f39,f38])).

fof(f69,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f71,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f35,plain,(
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

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2)
      | ~ m1_subset_1(X4,sK3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK1(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f66])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_20,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | r2_hidden(sK1(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_524,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | r2_hidden(sK1(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_525,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
    | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_4284,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4299,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5029,plain,
    ( m1_subset_1(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4284,c_4299])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_824,plain,
    ( m1_subset_1(X0,X1)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X2)))
    | ~ v1_relat_1(sK5)
    | sK1(k1_relat_1(sK5),X2,sK5) != X0
    | k1_relat_1(sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_525])).

cnf(c_825,plain,
    ( m1_subset_1(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_824])).

cnf(c_826,plain,
    ( m1_subset_1(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_825])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4721,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4886,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_4721])).

cnf(c_4887,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4886])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5194,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5195,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5194])).

cnf(c_7906,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | m1_subset_1(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5029,c_36,c_826,c_4887,c_5195])).

cnf(c_7907,plain,
    ( m1_subset_1(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7906])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1250,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_1251,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_1250])).

cnf(c_1253,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1251,c_27])).

cnf(c_4292,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4295,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5224,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4292,c_4295])).

cnf(c_5420,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1253,c_5224])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_14,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_554,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_555,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X0)
    | k3_funct_2(X0,X1,sK5,X2) = k1_funct_1(sK5,X2) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_1239,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | v1_xboole_0(X1)
    | X4 != X3
    | k3_funct_2(X1,X4,sK5,X0) = k1_funct_1(sK5,X0)
    | k1_relset_1(k1_xboole_0,X3,X2) != k1_xboole_0
    | sK5 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_555])).

cnf(c_1240,plain,
    ( ~ m1_subset_1(X0,k1_xboole_0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | v1_xboole_0(k1_xboole_0)
    | k3_funct_2(k1_xboole_0,X1,sK5,X0) = k1_funct_1(sK5,X0)
    | k1_relset_1(k1_xboole_0,X1,sK5) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1239])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_443,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_444,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_719,plain,
    ( v1_xboole_0(X0)
    | sK0(X0) != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_444])).

cnf(c_720,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_719])).

cnf(c_1242,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1240,c_720])).

cnf(c_1664,plain,
    ( sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_1242])).

cnf(c_5490,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5420,c_1664])).

cnf(c_7912,plain,
    ( m1_subset_1(sK1(sK3,X0,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7907,c_5490])).

cnf(c_1331,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,sK5,X0) = k1_funct_1(sK5,X0)
    | sK5 != sK5
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_555])).

cnf(c_1332,plain,
    ( ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_xboole_0(sK3)
    | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_1331])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1336,plain,
    ( ~ m1_subset_1(X0,sK3)
    | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1332,c_31,c_27])).

cnf(c_4276,plain,
    ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1336])).

cnf(c_7918,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,X0,sK5)) = k1_funct_1(sK5,sK1(sK3,X0,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7912,c_4276])).

cnf(c_5495,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5490,c_4284])).

cnf(c_6477,plain,
    ( r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5495,c_36,c_4887,c_5195])).

cnf(c_6478,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_6477])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4294,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6489,plain,
    ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
    | r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6478,c_4294])).

cnf(c_7180,plain,
    ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
    | m1_subset_1(sK1(sK3,X0,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6489,c_4299])).

cnf(c_7191,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,X0,sK5)) = k1_funct_1(sK5,sK1(sK3,X0,sK5))
    | k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_7180,c_4276])).

cnf(c_26,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4293,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7649,plain,
    ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
    | m1_subset_1(sK1(sK3,X0,sK5),sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7191,c_4293])).

cnf(c_7669,plain,
    ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
    | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7649,c_7180])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r2_hidden(k1_funct_1(X0,sK1(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_539,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r2_hidden(k1_funct_1(X0,sK1(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_540,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
    | ~ r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_4283,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_5496,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5490,c_4283])).

cnf(c_5896,plain,
    ( r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5496,c_36,c_4887,c_5195])).

cnf(c_5897,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5896])).

cnf(c_7680,plain,
    ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7669,c_5897])).

cnf(c_7750,plain,
    ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7680,c_4294])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4296,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7751,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7750,c_4296])).

cnf(c_5208,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4292,c_4294])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_244,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_245,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_244])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k2_relset_1(sK3,sK4,sK5) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_245,c_25])).

cnf(c_467,plain,
    ( ~ m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_4285,plain,
    ( m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_5364,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5208,c_4285])).

cnf(c_7760,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7751,c_5364])).

cnf(c_7978,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK2,sK5)) = k1_funct_1(sK5,sK1(sK3,sK2,sK5)) ),
    inference(superposition,[status(thm)],[c_7918,c_7760])).

cnf(c_8438,plain,
    ( m1_subset_1(sK1(sK3,sK2,sK5),sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(sK3,sK2,sK5)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7978,c_4293])).

cnf(c_7765,plain,
    ( r2_hidden(sK1(sK3,sK2,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6478,c_7760])).

cnf(c_8390,plain,
    ( m1_subset_1(sK1(sK3,sK2,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7765,c_4299])).

cnf(c_8450,plain,
    ( r2_hidden(k1_funct_1(sK5,sK1(sK3,sK2,sK5)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8438,c_8390])).

cnf(c_8459,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8450,c_5897])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8459,c_7751,c_5364])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:13:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.04/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/0.98  
% 3.04/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.04/0.98  
% 3.04/0.98  ------  iProver source info
% 3.04/0.98  
% 3.04/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.04/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.04/0.98  git: non_committed_changes: false
% 3.04/0.98  git: last_make_outside_of_git: false
% 3.04/0.98  
% 3.04/0.98  ------ 
% 3.04/0.98  
% 3.04/0.98  ------ Input Options
% 3.04/0.98  
% 3.04/0.98  --out_options                           all
% 3.04/0.98  --tptp_safe_out                         true
% 3.04/0.98  --problem_path                          ""
% 3.04/0.98  --include_path                          ""
% 3.04/0.98  --clausifier                            res/vclausify_rel
% 3.04/0.98  --clausifier_options                    --mode clausify
% 3.04/0.98  --stdin                                 false
% 3.04/0.98  --stats_out                             all
% 3.04/0.98  
% 3.04/0.98  ------ General Options
% 3.04/0.98  
% 3.04/0.98  --fof                                   false
% 3.04/0.98  --time_out_real                         305.
% 3.04/0.98  --time_out_virtual                      -1.
% 3.04/0.98  --symbol_type_check                     false
% 3.04/0.98  --clausify_out                          false
% 3.04/0.98  --sig_cnt_out                           false
% 3.04/0.98  --trig_cnt_out                          false
% 3.04/0.98  --trig_cnt_out_tolerance                1.
% 3.04/0.98  --trig_cnt_out_sk_spl                   false
% 3.04/0.98  --abstr_cl_out                          false
% 3.04/0.98  
% 3.04/0.98  ------ Global Options
% 3.04/0.98  
% 3.04/0.98  --schedule                              default
% 3.04/0.98  --add_important_lit                     false
% 3.04/0.98  --prop_solver_per_cl                    1000
% 3.04/0.98  --min_unsat_core                        false
% 3.04/0.98  --soft_assumptions                      false
% 3.04/0.98  --soft_lemma_size                       3
% 3.04/0.98  --prop_impl_unit_size                   0
% 3.04/0.98  --prop_impl_unit                        []
% 3.04/0.98  --share_sel_clauses                     true
% 3.04/0.98  --reset_solvers                         false
% 3.04/0.98  --bc_imp_inh                            [conj_cone]
% 3.04/0.98  --conj_cone_tolerance                   3.
% 3.04/0.98  --extra_neg_conj                        none
% 3.04/0.98  --large_theory_mode                     true
% 3.04/0.98  --prolific_symb_bound                   200
% 3.04/0.98  --lt_threshold                          2000
% 3.04/0.98  --clause_weak_htbl                      true
% 3.04/0.98  --gc_record_bc_elim                     false
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing Options
% 3.04/0.98  
% 3.04/0.98  --preprocessing_flag                    true
% 3.04/0.98  --time_out_prep_mult                    0.1
% 3.04/0.98  --splitting_mode                        input
% 3.04/0.98  --splitting_grd                         true
% 3.04/0.98  --splitting_cvd                         false
% 3.04/0.98  --splitting_cvd_svl                     false
% 3.04/0.98  --splitting_nvd                         32
% 3.04/0.98  --sub_typing                            true
% 3.04/0.98  --prep_gs_sim                           true
% 3.04/0.98  --prep_unflatten                        true
% 3.04/0.98  --prep_res_sim                          true
% 3.04/0.98  --prep_upred                            true
% 3.04/0.98  --prep_sem_filter                       exhaustive
% 3.04/0.98  --prep_sem_filter_out                   false
% 3.04/0.98  --pred_elim                             true
% 3.04/0.98  --res_sim_input                         true
% 3.04/0.98  --eq_ax_congr_red                       true
% 3.04/0.98  --pure_diseq_elim                       true
% 3.04/0.98  --brand_transform                       false
% 3.04/0.98  --non_eq_to_eq                          false
% 3.04/0.98  --prep_def_merge                        true
% 3.04/0.98  --prep_def_merge_prop_impl              false
% 3.04/0.98  --prep_def_merge_mbd                    true
% 3.04/0.98  --prep_def_merge_tr_red                 false
% 3.04/0.98  --prep_def_merge_tr_cl                  false
% 3.04/0.98  --smt_preprocessing                     true
% 3.04/0.98  --smt_ac_axioms                         fast
% 3.04/0.98  --preprocessed_out                      false
% 3.04/0.98  --preprocessed_stats                    false
% 3.04/0.98  
% 3.04/0.98  ------ Abstraction refinement Options
% 3.04/0.98  
% 3.04/0.98  --abstr_ref                             []
% 3.04/0.98  --abstr_ref_prep                        false
% 3.04/0.98  --abstr_ref_until_sat                   false
% 3.04/0.98  --abstr_ref_sig_restrict                funpre
% 3.04/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.98  --abstr_ref_under                       []
% 3.04/0.98  
% 3.04/0.98  ------ SAT Options
% 3.04/0.98  
% 3.04/0.98  --sat_mode                              false
% 3.04/0.98  --sat_fm_restart_options                ""
% 3.04/0.98  --sat_gr_def                            false
% 3.04/0.98  --sat_epr_types                         true
% 3.04/0.98  --sat_non_cyclic_types                  false
% 3.04/0.98  --sat_finite_models                     false
% 3.04/0.98  --sat_fm_lemmas                         false
% 3.04/0.98  --sat_fm_prep                           false
% 3.04/0.98  --sat_fm_uc_incr                        true
% 3.04/0.98  --sat_out_model                         small
% 3.04/0.98  --sat_out_clauses                       false
% 3.04/0.98  
% 3.04/0.98  ------ QBF Options
% 3.04/0.98  
% 3.04/0.98  --qbf_mode                              false
% 3.04/0.98  --qbf_elim_univ                         false
% 3.04/0.98  --qbf_dom_inst                          none
% 3.04/0.98  --qbf_dom_pre_inst                      false
% 3.04/0.98  --qbf_sk_in                             false
% 3.04/0.98  --qbf_pred_elim                         true
% 3.04/0.98  --qbf_split                             512
% 3.04/0.98  
% 3.04/0.98  ------ BMC1 Options
% 3.04/0.98  
% 3.04/0.98  --bmc1_incremental                      false
% 3.04/0.98  --bmc1_axioms                           reachable_all
% 3.04/0.98  --bmc1_min_bound                        0
% 3.04/0.98  --bmc1_max_bound                        -1
% 3.04/0.98  --bmc1_max_bound_default                -1
% 3.04/0.98  --bmc1_symbol_reachability              true
% 3.04/0.98  --bmc1_property_lemmas                  false
% 3.04/0.98  --bmc1_k_induction                      false
% 3.04/0.98  --bmc1_non_equiv_states                 false
% 3.04/0.98  --bmc1_deadlock                         false
% 3.04/0.98  --bmc1_ucm                              false
% 3.04/0.98  --bmc1_add_unsat_core                   none
% 3.04/0.98  --bmc1_unsat_core_children              false
% 3.04/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.98  --bmc1_out_stat                         full
% 3.04/0.98  --bmc1_ground_init                      false
% 3.04/0.98  --bmc1_pre_inst_next_state              false
% 3.04/0.98  --bmc1_pre_inst_state                   false
% 3.04/0.98  --bmc1_pre_inst_reach_state             false
% 3.04/0.98  --bmc1_out_unsat_core                   false
% 3.04/0.98  --bmc1_aig_witness_out                  false
% 3.04/0.98  --bmc1_verbose                          false
% 3.04/0.98  --bmc1_dump_clauses_tptp                false
% 3.04/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.98  --bmc1_dump_file                        -
% 3.04/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.98  --bmc1_ucm_extend_mode                  1
% 3.04/0.98  --bmc1_ucm_init_mode                    2
% 3.04/0.98  --bmc1_ucm_cone_mode                    none
% 3.04/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.98  --bmc1_ucm_relax_model                  4
% 3.04/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.98  --bmc1_ucm_layered_model                none
% 3.04/0.98  --bmc1_ucm_max_lemma_size               10
% 3.04/0.98  
% 3.04/0.98  ------ AIG Options
% 3.04/0.98  
% 3.04/0.98  --aig_mode                              false
% 3.04/0.98  
% 3.04/0.98  ------ Instantiation Options
% 3.04/0.98  
% 3.04/0.98  --instantiation_flag                    true
% 3.04/0.98  --inst_sos_flag                         false
% 3.04/0.98  --inst_sos_phase                        true
% 3.04/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.98  --inst_lit_sel_side                     num_symb
% 3.04/0.98  --inst_solver_per_active                1400
% 3.04/0.98  --inst_solver_calls_frac                1.
% 3.04/0.98  --inst_passive_queue_type               priority_queues
% 3.04/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.98  --inst_passive_queues_freq              [25;2]
% 3.04/0.98  --inst_dismatching                      true
% 3.04/0.98  --inst_eager_unprocessed_to_passive     true
% 3.04/0.98  --inst_prop_sim_given                   true
% 3.04/0.98  --inst_prop_sim_new                     false
% 3.04/0.98  --inst_subs_new                         false
% 3.04/0.98  --inst_eq_res_simp                      false
% 3.04/0.98  --inst_subs_given                       false
% 3.04/0.98  --inst_orphan_elimination               true
% 3.04/0.98  --inst_learning_loop_flag               true
% 3.04/0.98  --inst_learning_start                   3000
% 3.04/0.98  --inst_learning_factor                  2
% 3.04/0.98  --inst_start_prop_sim_after_learn       3
% 3.04/0.98  --inst_sel_renew                        solver
% 3.04/0.98  --inst_lit_activity_flag                true
% 3.04/0.98  --inst_restr_to_given                   false
% 3.04/0.98  --inst_activity_threshold               500
% 3.04/0.98  --inst_out_proof                        true
% 3.04/0.98  
% 3.04/0.98  ------ Resolution Options
% 3.04/0.98  
% 3.04/0.98  --resolution_flag                       true
% 3.04/0.98  --res_lit_sel                           adaptive
% 3.04/0.98  --res_lit_sel_side                      none
% 3.04/0.98  --res_ordering                          kbo
% 3.04/0.98  --res_to_prop_solver                    active
% 3.04/0.98  --res_prop_simpl_new                    false
% 3.04/0.98  --res_prop_simpl_given                  true
% 3.04/0.98  --res_passive_queue_type                priority_queues
% 3.04/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.98  --res_passive_queues_freq               [15;5]
% 3.04/0.98  --res_forward_subs                      full
% 3.04/0.98  --res_backward_subs                     full
% 3.04/0.98  --res_forward_subs_resolution           true
% 3.04/0.98  --res_backward_subs_resolution          true
% 3.04/0.98  --res_orphan_elimination                true
% 3.04/0.98  --res_time_limit                        2.
% 3.04/0.98  --res_out_proof                         true
% 3.04/0.98  
% 3.04/0.98  ------ Superposition Options
% 3.04/0.98  
% 3.04/0.98  --superposition_flag                    true
% 3.04/0.98  --sup_passive_queue_type                priority_queues
% 3.04/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.98  --demod_completeness_check              fast
% 3.04/0.98  --demod_use_ground                      true
% 3.04/0.98  --sup_to_prop_solver                    passive
% 3.04/0.98  --sup_prop_simpl_new                    true
% 3.04/0.98  --sup_prop_simpl_given                  true
% 3.04/0.98  --sup_fun_splitting                     false
% 3.04/0.98  --sup_smt_interval                      50000
% 3.04/0.98  
% 3.04/0.98  ------ Superposition Simplification Setup
% 3.04/0.98  
% 3.04/0.98  --sup_indices_passive                   []
% 3.04/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_full_bw                           [BwDemod]
% 3.04/0.98  --sup_immed_triv                        [TrivRules]
% 3.04/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_immed_bw_main                     []
% 3.04/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.98  
% 3.04/0.98  ------ Combination Options
% 3.04/0.98  
% 3.04/0.98  --comb_res_mult                         3
% 3.04/0.98  --comb_sup_mult                         2
% 3.04/0.98  --comb_inst_mult                        10
% 3.04/0.98  
% 3.04/0.98  ------ Debug Options
% 3.04/0.98  
% 3.04/0.98  --dbg_backtrace                         false
% 3.04/0.98  --dbg_dump_prop_clauses                 false
% 3.04/0.98  --dbg_dump_prop_clauses_file            -
% 3.04/0.98  --dbg_out_stat                          false
% 3.04/0.98  ------ Parsing...
% 3.04/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.04/0.98  ------ Proving...
% 3.04/0.98  ------ Problem Properties 
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  clauses                                 36
% 3.04/0.98  conjectures                             4
% 3.04/0.98  EPR                                     9
% 3.04/0.98  Horn                                    25
% 3.04/0.98  unary                                   11
% 3.04/0.98  binary                                  11
% 3.04/0.98  lits                                    86
% 3.04/0.98  lits eq                                 24
% 3.04/0.98  fd_pure                                 0
% 3.04/0.98  fd_pseudo                               0
% 3.04/0.98  fd_cond                                 4
% 3.04/0.98  fd_pseudo_cond                          0
% 3.04/0.98  AC symbols                              0
% 3.04/0.98  
% 3.04/0.98  ------ Schedule dynamic 5 is on 
% 3.04/0.98  
% 3.04/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  ------ 
% 3.04/0.98  Current options:
% 3.04/0.98  ------ 
% 3.04/0.98  
% 3.04/0.98  ------ Input Options
% 3.04/0.98  
% 3.04/0.98  --out_options                           all
% 3.04/0.98  --tptp_safe_out                         true
% 3.04/0.98  --problem_path                          ""
% 3.04/0.98  --include_path                          ""
% 3.04/0.98  --clausifier                            res/vclausify_rel
% 3.04/0.98  --clausifier_options                    --mode clausify
% 3.04/0.98  --stdin                                 false
% 3.04/0.98  --stats_out                             all
% 3.04/0.98  
% 3.04/0.98  ------ General Options
% 3.04/0.98  
% 3.04/0.98  --fof                                   false
% 3.04/0.98  --time_out_real                         305.
% 3.04/0.98  --time_out_virtual                      -1.
% 3.04/0.98  --symbol_type_check                     false
% 3.04/0.98  --clausify_out                          false
% 3.04/0.98  --sig_cnt_out                           false
% 3.04/0.98  --trig_cnt_out                          false
% 3.04/0.98  --trig_cnt_out_tolerance                1.
% 3.04/0.98  --trig_cnt_out_sk_spl                   false
% 3.04/0.98  --abstr_cl_out                          false
% 3.04/0.98  
% 3.04/0.98  ------ Global Options
% 3.04/0.98  
% 3.04/0.98  --schedule                              default
% 3.04/0.98  --add_important_lit                     false
% 3.04/0.98  --prop_solver_per_cl                    1000
% 3.04/0.98  --min_unsat_core                        false
% 3.04/0.98  --soft_assumptions                      false
% 3.04/0.98  --soft_lemma_size                       3
% 3.04/0.98  --prop_impl_unit_size                   0
% 3.04/0.98  --prop_impl_unit                        []
% 3.04/0.98  --share_sel_clauses                     true
% 3.04/0.98  --reset_solvers                         false
% 3.04/0.98  --bc_imp_inh                            [conj_cone]
% 3.04/0.98  --conj_cone_tolerance                   3.
% 3.04/0.98  --extra_neg_conj                        none
% 3.04/0.98  --large_theory_mode                     true
% 3.04/0.98  --prolific_symb_bound                   200
% 3.04/0.98  --lt_threshold                          2000
% 3.04/0.98  --clause_weak_htbl                      true
% 3.04/0.98  --gc_record_bc_elim                     false
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing Options
% 3.04/0.98  
% 3.04/0.98  --preprocessing_flag                    true
% 3.04/0.98  --time_out_prep_mult                    0.1
% 3.04/0.98  --splitting_mode                        input
% 3.04/0.98  --splitting_grd                         true
% 3.04/0.98  --splitting_cvd                         false
% 3.04/0.98  --splitting_cvd_svl                     false
% 3.04/0.98  --splitting_nvd                         32
% 3.04/0.98  --sub_typing                            true
% 3.04/0.98  --prep_gs_sim                           true
% 3.04/0.98  --prep_unflatten                        true
% 3.04/0.98  --prep_res_sim                          true
% 3.04/0.98  --prep_upred                            true
% 3.04/0.98  --prep_sem_filter                       exhaustive
% 3.04/0.98  --prep_sem_filter_out                   false
% 3.04/0.98  --pred_elim                             true
% 3.04/0.98  --res_sim_input                         true
% 3.04/0.98  --eq_ax_congr_red                       true
% 3.04/0.98  --pure_diseq_elim                       true
% 3.04/0.98  --brand_transform                       false
% 3.04/0.98  --non_eq_to_eq                          false
% 3.04/0.98  --prep_def_merge                        true
% 3.04/0.98  --prep_def_merge_prop_impl              false
% 3.04/0.98  --prep_def_merge_mbd                    true
% 3.04/0.98  --prep_def_merge_tr_red                 false
% 3.04/0.98  --prep_def_merge_tr_cl                  false
% 3.04/0.98  --smt_preprocessing                     true
% 3.04/0.98  --smt_ac_axioms                         fast
% 3.04/0.98  --preprocessed_out                      false
% 3.04/0.98  --preprocessed_stats                    false
% 3.04/0.98  
% 3.04/0.98  ------ Abstraction refinement Options
% 3.04/0.98  
% 3.04/0.98  --abstr_ref                             []
% 3.04/0.98  --abstr_ref_prep                        false
% 3.04/0.98  --abstr_ref_until_sat                   false
% 3.04/0.98  --abstr_ref_sig_restrict                funpre
% 3.04/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.98  --abstr_ref_under                       []
% 3.04/0.98  
% 3.04/0.98  ------ SAT Options
% 3.04/0.98  
% 3.04/0.98  --sat_mode                              false
% 3.04/0.98  --sat_fm_restart_options                ""
% 3.04/0.98  --sat_gr_def                            false
% 3.04/0.98  --sat_epr_types                         true
% 3.04/0.98  --sat_non_cyclic_types                  false
% 3.04/0.98  --sat_finite_models                     false
% 3.04/0.98  --sat_fm_lemmas                         false
% 3.04/0.98  --sat_fm_prep                           false
% 3.04/0.98  --sat_fm_uc_incr                        true
% 3.04/0.98  --sat_out_model                         small
% 3.04/0.98  --sat_out_clauses                       false
% 3.04/0.98  
% 3.04/0.98  ------ QBF Options
% 3.04/0.98  
% 3.04/0.98  --qbf_mode                              false
% 3.04/0.98  --qbf_elim_univ                         false
% 3.04/0.98  --qbf_dom_inst                          none
% 3.04/0.98  --qbf_dom_pre_inst                      false
% 3.04/0.98  --qbf_sk_in                             false
% 3.04/0.98  --qbf_pred_elim                         true
% 3.04/0.98  --qbf_split                             512
% 3.04/0.98  
% 3.04/0.98  ------ BMC1 Options
% 3.04/0.98  
% 3.04/0.98  --bmc1_incremental                      false
% 3.04/0.98  --bmc1_axioms                           reachable_all
% 3.04/0.98  --bmc1_min_bound                        0
% 3.04/0.98  --bmc1_max_bound                        -1
% 3.04/0.98  --bmc1_max_bound_default                -1
% 3.04/0.98  --bmc1_symbol_reachability              true
% 3.04/0.98  --bmc1_property_lemmas                  false
% 3.04/0.98  --bmc1_k_induction                      false
% 3.04/0.98  --bmc1_non_equiv_states                 false
% 3.04/0.98  --bmc1_deadlock                         false
% 3.04/0.98  --bmc1_ucm                              false
% 3.04/0.98  --bmc1_add_unsat_core                   none
% 3.04/0.98  --bmc1_unsat_core_children              false
% 3.04/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.98  --bmc1_out_stat                         full
% 3.04/0.98  --bmc1_ground_init                      false
% 3.04/0.98  --bmc1_pre_inst_next_state              false
% 3.04/0.98  --bmc1_pre_inst_state                   false
% 3.04/0.98  --bmc1_pre_inst_reach_state             false
% 3.04/0.98  --bmc1_out_unsat_core                   false
% 3.04/0.98  --bmc1_aig_witness_out                  false
% 3.04/0.98  --bmc1_verbose                          false
% 3.04/0.98  --bmc1_dump_clauses_tptp                false
% 3.04/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.98  --bmc1_dump_file                        -
% 3.04/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.98  --bmc1_ucm_extend_mode                  1
% 3.04/0.98  --bmc1_ucm_init_mode                    2
% 3.04/0.98  --bmc1_ucm_cone_mode                    none
% 3.04/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.98  --bmc1_ucm_relax_model                  4
% 3.04/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.98  --bmc1_ucm_layered_model                none
% 3.04/0.98  --bmc1_ucm_max_lemma_size               10
% 3.04/0.98  
% 3.04/0.98  ------ AIG Options
% 3.04/0.98  
% 3.04/0.98  --aig_mode                              false
% 3.04/0.98  
% 3.04/0.98  ------ Instantiation Options
% 3.04/0.98  
% 3.04/0.98  --instantiation_flag                    true
% 3.04/0.98  --inst_sos_flag                         false
% 3.04/0.98  --inst_sos_phase                        true
% 3.04/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.98  --inst_lit_sel_side                     none
% 3.04/0.98  --inst_solver_per_active                1400
% 3.04/0.98  --inst_solver_calls_frac                1.
% 3.04/0.98  --inst_passive_queue_type               priority_queues
% 3.04/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.98  --inst_passive_queues_freq              [25;2]
% 3.04/0.98  --inst_dismatching                      true
% 3.04/0.98  --inst_eager_unprocessed_to_passive     true
% 3.04/0.98  --inst_prop_sim_given                   true
% 3.04/0.98  --inst_prop_sim_new                     false
% 3.04/0.98  --inst_subs_new                         false
% 3.04/0.98  --inst_eq_res_simp                      false
% 3.04/0.98  --inst_subs_given                       false
% 3.04/0.98  --inst_orphan_elimination               true
% 3.04/0.98  --inst_learning_loop_flag               true
% 3.04/0.98  --inst_learning_start                   3000
% 3.04/0.98  --inst_learning_factor                  2
% 3.04/0.98  --inst_start_prop_sim_after_learn       3
% 3.04/0.98  --inst_sel_renew                        solver
% 3.04/0.98  --inst_lit_activity_flag                true
% 3.04/0.98  --inst_restr_to_given                   false
% 3.04/0.98  --inst_activity_threshold               500
% 3.04/0.98  --inst_out_proof                        true
% 3.04/0.98  
% 3.04/0.98  ------ Resolution Options
% 3.04/0.98  
% 3.04/0.98  --resolution_flag                       false
% 3.04/0.98  --res_lit_sel                           adaptive
% 3.04/0.98  --res_lit_sel_side                      none
% 3.04/0.98  --res_ordering                          kbo
% 3.04/0.98  --res_to_prop_solver                    active
% 3.04/0.98  --res_prop_simpl_new                    false
% 3.04/0.98  --res_prop_simpl_given                  true
% 3.04/0.98  --res_passive_queue_type                priority_queues
% 3.04/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.98  --res_passive_queues_freq               [15;5]
% 3.04/0.98  --res_forward_subs                      full
% 3.04/0.98  --res_backward_subs                     full
% 3.04/0.98  --res_forward_subs_resolution           true
% 3.04/0.98  --res_backward_subs_resolution          true
% 3.04/0.98  --res_orphan_elimination                true
% 3.04/0.98  --res_time_limit                        2.
% 3.04/0.98  --res_out_proof                         true
% 3.04/0.98  
% 3.04/0.98  ------ Superposition Options
% 3.04/0.98  
% 3.04/0.98  --superposition_flag                    true
% 3.04/0.98  --sup_passive_queue_type                priority_queues
% 3.04/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.98  --demod_completeness_check              fast
% 3.04/0.98  --demod_use_ground                      true
% 3.04/0.98  --sup_to_prop_solver                    passive
% 3.04/0.98  --sup_prop_simpl_new                    true
% 3.04/0.98  --sup_prop_simpl_given                  true
% 3.04/0.98  --sup_fun_splitting                     false
% 3.04/0.98  --sup_smt_interval                      50000
% 3.04/0.98  
% 3.04/0.98  ------ Superposition Simplification Setup
% 3.04/0.98  
% 3.04/0.98  --sup_indices_passive                   []
% 3.04/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_full_bw                           [BwDemod]
% 3.04/0.98  --sup_immed_triv                        [TrivRules]
% 3.04/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_immed_bw_main                     []
% 3.04/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.98  
% 3.04/0.98  ------ Combination Options
% 3.04/0.98  
% 3.04/0.98  --comb_res_mult                         3
% 3.04/0.98  --comb_sup_mult                         2
% 3.04/0.98  --comb_inst_mult                        10
% 3.04/0.98  
% 3.04/0.98  ------ Debug Options
% 3.04/0.98  
% 3.04/0.98  --dbg_backtrace                         false
% 3.04/0.98  --dbg_dump_prop_clauses                 false
% 3.04/0.98  --dbg_dump_prop_clauses_file            -
% 3.04/0.98  --dbg_out_stat                          false
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  ------ Proving...
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  % SZS status Theorem for theBenchmark.p
% 3.04/0.98  
% 3.04/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.04/0.98  
% 3.04/0.98  fof(f13,axiom,(
% 3.04/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f26,plain,(
% 3.04/0.98    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.04/0.98    inference(ennf_transformation,[],[f13])).
% 3.04/0.98  
% 3.04/0.98  fof(f27,plain,(
% 3.04/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.04/0.98    inference(flattening,[],[f26])).
% 3.04/0.98  
% 3.04/0.98  fof(f36,plain,(
% 3.04/0.98    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),X0)))),
% 3.04/0.98    introduced(choice_axiom,[])).
% 3.04/0.98  
% 3.04/0.98  fof(f37,plain,(
% 3.04/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.04/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f36])).
% 3.04/0.98  
% 3.04/0.98  fof(f65,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK1(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f37])).
% 3.04/0.98  
% 3.04/0.98  fof(f80,plain,(
% 3.04/0.98    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK1(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.04/0.98    inference(equality_resolution,[],[f65])).
% 3.04/0.98  
% 3.04/0.98  fof(f14,conjecture,(
% 3.04/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f15,negated_conjecture,(
% 3.04/0.98    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.04/0.98    inference(negated_conjecture,[],[f14])).
% 3.04/0.98  
% 3.04/0.98  fof(f28,plain,(
% 3.04/0.98    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.04/0.98    inference(ennf_transformation,[],[f15])).
% 3.04/0.98  
% 3.04/0.98  fof(f29,plain,(
% 3.04/0.98    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.04/0.98    inference(flattening,[],[f28])).
% 3.04/0.98  
% 3.04/0.98  fof(f40,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK5),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK5,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 3.04/0.98    introduced(choice_axiom,[])).
% 3.04/0.98  
% 3.04/0.98  fof(f39,plain,(
% 3.04/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK4,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK4,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK4))) & v1_funct_2(X3,X1,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))) )),
% 3.04/0.98    introduced(choice_axiom,[])).
% 3.04/0.98  
% 3.04/0.98  fof(f38,plain,(
% 3.04/0.98    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK3,X2,X3),sK2) & ! [X4] : (r2_hidden(k3_funct_2(sK3,X2,X3,X4),sK2) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X2))) & v1_funct_2(X3,sK3,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))),
% 3.04/0.98    introduced(choice_axiom,[])).
% 3.04/0.98  
% 3.04/0.98  fof(f41,plain,(
% 3.04/0.98    ((~r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) & ! [X4] : (r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)),
% 3.04/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f40,f39,f38])).
% 3.04/0.98  
% 3.04/0.98  fof(f69,plain,(
% 3.04/0.98    v1_funct_1(sK5)),
% 3.04/0.98    inference(cnf_transformation,[],[f41])).
% 3.04/0.98  
% 3.04/0.98  fof(f3,axiom,(
% 3.04/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f16,plain,(
% 3.04/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.04/0.98    inference(ennf_transformation,[],[f3])).
% 3.04/0.98  
% 3.04/0.98  fof(f45,plain,(
% 3.04/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f16])).
% 3.04/0.98  
% 3.04/0.98  fof(f71,plain,(
% 3.04/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.04/0.98    inference(cnf_transformation,[],[f41])).
% 3.04/0.98  
% 3.04/0.98  fof(f5,axiom,(
% 3.04/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f17,plain,(
% 3.04/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.04/0.98    inference(ennf_transformation,[],[f5])).
% 3.04/0.98  
% 3.04/0.98  fof(f48,plain,(
% 3.04/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f17])).
% 3.04/0.98  
% 3.04/0.98  fof(f6,axiom,(
% 3.04/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f49,plain,(
% 3.04/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f6])).
% 3.04/0.98  
% 3.04/0.98  fof(f11,axiom,(
% 3.04/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f22,plain,(
% 3.04/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(ennf_transformation,[],[f11])).
% 3.04/0.98  
% 3.04/0.98  fof(f23,plain,(
% 3.04/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(flattening,[],[f22])).
% 3.04/0.98  
% 3.04/0.98  fof(f35,plain,(
% 3.04/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(nnf_transformation,[],[f23])).
% 3.04/0.98  
% 3.04/0.98  fof(f54,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f35])).
% 3.04/0.98  
% 3.04/0.98  fof(f70,plain,(
% 3.04/0.98    v1_funct_2(sK5,sK3,sK4)),
% 3.04/0.98    inference(cnf_transformation,[],[f41])).
% 3.04/0.98  
% 3.04/0.98  fof(f9,axiom,(
% 3.04/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f20,plain,(
% 3.04/0.98    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(ennf_transformation,[],[f9])).
% 3.04/0.98  
% 3.04/0.98  fof(f52,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f20])).
% 3.04/0.98  
% 3.04/0.98  fof(f68,plain,(
% 3.04/0.98    ~v1_xboole_0(sK4)),
% 3.04/0.98    inference(cnf_transformation,[],[f41])).
% 3.04/0.98  
% 3.04/0.98  fof(f57,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f35])).
% 3.04/0.98  
% 3.04/0.98  fof(f77,plain,(
% 3.04/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.04/0.98    inference(equality_resolution,[],[f57])).
% 3.04/0.98  
% 3.04/0.98  fof(f12,axiom,(
% 3.04/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f24,plain,(
% 3.04/0.98    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.04/0.98    inference(ennf_transformation,[],[f12])).
% 3.04/0.98  
% 3.04/0.98  fof(f25,plain,(
% 3.04/0.98    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.04/0.98    inference(flattening,[],[f24])).
% 3.04/0.98  
% 3.04/0.98  fof(f60,plain,(
% 3.04/0.98    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f25])).
% 3.04/0.98  
% 3.04/0.98  fof(f1,axiom,(
% 3.04/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f30,plain,(
% 3.04/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.04/0.98    inference(nnf_transformation,[],[f1])).
% 3.04/0.98  
% 3.04/0.98  fof(f31,plain,(
% 3.04/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.04/0.98    inference(rectify,[],[f30])).
% 3.04/0.98  
% 3.04/0.98  fof(f32,plain,(
% 3.04/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.04/0.98    introduced(choice_axiom,[])).
% 3.04/0.98  
% 3.04/0.98  fof(f33,plain,(
% 3.04/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.04/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 3.04/0.98  
% 3.04/0.98  fof(f43,plain,(
% 3.04/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f33])).
% 3.04/0.98  
% 3.04/0.98  fof(f2,axiom,(
% 3.04/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f44,plain,(
% 3.04/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f2])).
% 3.04/0.98  
% 3.04/0.98  fof(f7,axiom,(
% 3.04/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f18,plain,(
% 3.04/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.04/0.98    inference(ennf_transformation,[],[f7])).
% 3.04/0.98  
% 3.04/0.98  fof(f50,plain,(
% 3.04/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f18])).
% 3.04/0.98  
% 3.04/0.98  fof(f67,plain,(
% 3.04/0.98    ~v1_xboole_0(sK3)),
% 3.04/0.98    inference(cnf_transformation,[],[f41])).
% 3.04/0.98  
% 3.04/0.98  fof(f10,axiom,(
% 3.04/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f21,plain,(
% 3.04/0.98    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(ennf_transformation,[],[f10])).
% 3.04/0.98  
% 3.04/0.98  fof(f53,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f21])).
% 3.04/0.98  
% 3.04/0.98  fof(f72,plain,(
% 3.04/0.98    ( ! [X4] : (r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2) | ~m1_subset_1(X4,sK3)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f41])).
% 3.04/0.98  
% 3.04/0.98  fof(f66,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f37])).
% 3.04/0.98  
% 3.04/0.98  fof(f79,plain,(
% 3.04/0.98    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK1(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.04/0.98    inference(equality_resolution,[],[f66])).
% 3.04/0.98  
% 3.04/0.98  fof(f8,axiom,(
% 3.04/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f19,plain,(
% 3.04/0.98    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(ennf_transformation,[],[f8])).
% 3.04/0.98  
% 3.04/0.98  fof(f51,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f19])).
% 3.04/0.98  
% 3.04/0.98  fof(f4,axiom,(
% 3.04/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f34,plain,(
% 3.04/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.04/0.98    inference(nnf_transformation,[],[f4])).
% 3.04/0.98  
% 3.04/0.98  fof(f46,plain,(
% 3.04/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f34])).
% 3.04/0.98  
% 3.04/0.98  fof(f73,plain,(
% 3.04/0.98    ~r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2)),
% 3.04/0.98    inference(cnf_transformation,[],[f41])).
% 3.04/0.98  
% 3.04/0.98  cnf(c_20,plain,
% 3.04/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.04/0.98      | r2_hidden(sK1(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.04/0.98      | ~ v1_funct_1(X0)
% 3.04/0.98      | ~ v1_relat_1(X0) ),
% 3.04/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_29,negated_conjecture,
% 3.04/0.98      ( v1_funct_1(sK5) ),
% 3.04/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_524,plain,
% 3.04/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.04/0.98      | r2_hidden(sK1(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.04/0.98      | ~ v1_relat_1(X0)
% 3.04/0.98      | sK5 != X0 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_525,plain,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
% 3.04/0.98      | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5))
% 3.04/0.98      | ~ v1_relat_1(sK5) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_524]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_4284,plain,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.04/0.98      | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
% 3.04/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_3,plain,
% 3.04/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.04/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_4299,plain,
% 3.04/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.04/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_5029,plain,
% 3.04/0.98      ( m1_subset_1(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
% 3.04/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.04/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_4284,c_4299]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_27,negated_conjecture,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.04/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_36,plain,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_824,plain,
% 3.04/0.98      ( m1_subset_1(X0,X1)
% 3.04/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X2)))
% 3.04/0.98      | ~ v1_relat_1(sK5)
% 3.04/0.98      | sK1(k1_relat_1(sK5),X2,sK5) != X0
% 3.04/0.98      | k1_relat_1(sK5) != X1 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_525]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_825,plain,
% 3.04/0.98      ( m1_subset_1(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5))
% 3.04/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
% 3.04/0.98      | ~ v1_relat_1(sK5) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_824]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_826,plain,
% 3.04/0.98      ( m1_subset_1(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
% 3.04/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.04/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_825]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_6,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/0.98      | ~ v1_relat_1(X1)
% 3.04/0.98      | v1_relat_1(X0) ),
% 3.04/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_4721,plain,
% 3.04/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 3.04/0.98      | ~ v1_relat_1(X0)
% 3.04/0.98      | v1_relat_1(sK5) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_4886,plain,
% 3.04/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.04/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 3.04/0.98      | v1_relat_1(sK5) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_4721]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_4887,plain,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.04/0.98      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.04/0.98      | v1_relat_1(sK5) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_4886]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7,plain,
% 3.04/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.04/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_5194,plain,
% 3.04/0.98      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_5195,plain,
% 3.04/0.98      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_5194]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7906,plain,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.04/0.98      | m1_subset_1(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_5029,c_36,c_826,c_4887,c_5195]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7907,plain,
% 3.04/0.98      ( m1_subset_1(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
% 3.04/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_7906]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_17,plain,
% 3.04/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.04/0.98      | k1_xboole_0 = X2 ),
% 3.04/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_28,negated_conjecture,
% 3.04/0.98      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.04/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1250,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.04/0.98      | sK5 != X0
% 3.04/0.98      | sK4 != X2
% 3.04/0.98      | sK3 != X1
% 3.04/0.98      | k1_xboole_0 = X2 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1251,plain,
% 3.04/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.04/0.98      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.04/0.98      | k1_xboole_0 = sK4 ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_1250]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1253,plain,
% 3.04/0.98      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_1251,c_27]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_4292,plain,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_10,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.04/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_4295,plain,
% 3.04/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.04/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_5224,plain,
% 3.04/0.98      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_4292,c_4295]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_5420,plain,
% 3.04/0.98      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_1253,c_5224]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_30,negated_conjecture,
% 3.04/0.98      ( ~ v1_xboole_0(sK4) ),
% 3.04/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_14,plain,
% 3.04/0.98      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.04/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.04/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_18,plain,
% 3.04/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.98      | ~ m1_subset_1(X3,X1)
% 3.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.98      | ~ v1_funct_1(X0)
% 3.04/0.98      | v1_xboole_0(X1)
% 3.04/0.98      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.04/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_554,plain,
% 3.04/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.98      | ~ m1_subset_1(X3,X1)
% 3.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.98      | v1_xboole_0(X1)
% 3.04/0.98      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 3.04/0.98      | sK5 != X0 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_555,plain,
% 3.04/0.98      ( ~ v1_funct_2(sK5,X0,X1)
% 3.04/0.98      | ~ m1_subset_1(X2,X0)
% 3.04/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.98      | v1_xboole_0(X0)
% 3.04/0.98      | k3_funct_2(X0,X1,sK5,X2) = k1_funct_1(sK5,X2) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_554]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1239,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,X1)
% 3.04/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
% 3.04/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 3.04/0.98      | v1_xboole_0(X1)
% 3.04/0.98      | X4 != X3
% 3.04/0.98      | k3_funct_2(X1,X4,sK5,X0) = k1_funct_1(sK5,X0)
% 3.04/0.98      | k1_relset_1(k1_xboole_0,X3,X2) != k1_xboole_0
% 3.04/0.98      | sK5 != X2
% 3.04/0.98      | k1_xboole_0 != X1 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_555]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1240,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,k1_xboole_0)
% 3.04/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.04/0.98      | v1_xboole_0(k1_xboole_0)
% 3.04/0.98      | k3_funct_2(k1_xboole_0,X1,sK5,X0) = k1_funct_1(sK5,X0)
% 3.04/0.98      | k1_relset_1(k1_xboole_0,X1,sK5) != k1_xboole_0 ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_1239]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_0,plain,
% 3.04/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.04/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2,plain,
% 3.04/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.04/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_8,plain,
% 3.04/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.04/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_443,plain,
% 3.04/0.98      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_444,plain,
% 3.04/0.98      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_443]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_719,plain,
% 3.04/0.98      ( v1_xboole_0(X0) | sK0(X0) != X1 | k1_xboole_0 != X0 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_444]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_720,plain,
% 3.04/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_719]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1242,plain,
% 3.04/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_1240,c_720]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1664,plain,
% 3.04/0.98      ( sK4 != k1_xboole_0 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_1242]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_5490,plain,
% 3.04/0.98      ( k1_relat_1(sK5) = sK3 ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_5420,c_1664]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7912,plain,
% 3.04/0.98      ( m1_subset_1(sK1(sK3,X0,sK5),sK3) = iProver_top
% 3.04/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
% 3.04/0.98      inference(light_normalisation,[status(thm)],[c_7907,c_5490]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1331,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,X1)
% 3.04/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.98      | v1_xboole_0(X1)
% 3.04/0.98      | k3_funct_2(X1,X2,sK5,X0) = k1_funct_1(sK5,X0)
% 3.04/0.98      | sK5 != sK5
% 3.04/0.98      | sK4 != X2
% 3.04/0.98      | sK3 != X1 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_555]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1332,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,sK3)
% 3.04/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.04/0.98      | v1_xboole_0(sK3)
% 3.04/0.98      | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_1331]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_31,negated_conjecture,
% 3.04/0.98      ( ~ v1_xboole_0(sK3) ),
% 3.04/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1336,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,sK3)
% 3.04/0.98      | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_1332,c_31,c_27]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_4276,plain,
% 3.04/0.98      ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
% 3.04/0.98      | m1_subset_1(X0,sK3) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_1336]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7918,plain,
% 3.04/0.98      ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,X0,sK5)) = k1_funct_1(sK5,sK1(sK3,X0,sK5))
% 3.04/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_7912,c_4276]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_5495,plain,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.04/0.98      | r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top
% 3.04/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.04/0.98      inference(demodulation,[status(thm)],[c_5490,c_4284]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_6477,plain,
% 3.04/0.98      ( r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top
% 3.04/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_5495,c_36,c_4887,c_5195]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_6478,plain,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.04/0.98      | r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_6477]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.04/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_4294,plain,
% 3.04/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.04/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_6489,plain,
% 3.04/0.98      ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
% 3.04/0.98      | r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_6478,c_4294]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7180,plain,
% 3.04/0.98      ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
% 3.04/0.98      | m1_subset_1(sK1(sK3,X0,sK5),sK3) = iProver_top ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_6489,c_4299]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7191,plain,
% 3.04/0.98      ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,X0,sK5)) = k1_funct_1(sK5,sK1(sK3,X0,sK5))
% 3.04/0.98      | k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5) ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_7180,c_4276]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_26,negated_conjecture,
% 3.04/0.98      ( ~ m1_subset_1(X0,sK3)
% 3.04/0.98      | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) ),
% 3.04/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_4293,plain,
% 3.04/0.98      ( m1_subset_1(X0,sK3) != iProver_top
% 3.04/0.98      | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7649,plain,
% 3.04/0.98      ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
% 3.04/0.98      | m1_subset_1(sK1(sK3,X0,sK5),sK3) != iProver_top
% 3.04/0.98      | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),sK2) = iProver_top ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_7191,c_4293]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7669,plain,
% 3.04/0.98      ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
% 3.04/0.98      | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),sK2) = iProver_top ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_7649,c_7180]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_19,plain,
% 3.04/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.04/0.98      | ~ r2_hidden(k1_funct_1(X0,sK1(k1_relat_1(X0),X1,X0)),X1)
% 3.04/0.98      | ~ v1_funct_1(X0)
% 3.04/0.98      | ~ v1_relat_1(X0) ),
% 3.04/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_539,plain,
% 3.04/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.04/0.98      | ~ r2_hidden(k1_funct_1(X0,sK1(k1_relat_1(X0),X1,X0)),X1)
% 3.04/0.98      | ~ v1_relat_1(X0)
% 3.04/0.98      | sK5 != X0 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_540,plain,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
% 3.04/0.98      | ~ r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0)
% 3.04/0.98      | ~ v1_relat_1(sK5) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_539]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_4283,plain,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.04/0.98      | r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top
% 3.04/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_5496,plain,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.04/0.98      | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),X0) != iProver_top
% 3.04/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.04/0.98      inference(demodulation,[status(thm)],[c_5490,c_4283]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_5896,plain,
% 3.04/0.98      ( r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),X0) != iProver_top
% 3.04/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_5496,c_36,c_4887,c_5195]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_5897,plain,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.04/0.98      | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),X0) != iProver_top ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_5896]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7680,plain,
% 3.04/0.98      ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5)
% 3.04/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_7669,c_5897]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7750,plain,
% 3.04/0.98      ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5) ),
% 3.04/0.98      inference(forward_subsumption_resolution,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_7680,c_4294]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_9,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.04/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_4296,plain,
% 3.04/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.04/0.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7751,plain,
% 3.04/0.98      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top
% 3.04/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_7750,c_4296]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_5208,plain,
% 3.04/0.98      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_4292,c_4294]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_5,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.04/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_244,plain,
% 3.04/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.04/0.98      inference(prop_impl,[status(thm)],[c_5]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_245,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_244]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_25,negated_conjecture,
% 3.04/0.98      ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) ),
% 3.04/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_466,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/0.98      | k2_relset_1(sK3,sK4,sK5) != X0
% 3.04/0.98      | sK2 != X1 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_245,c_25]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_467,plain,
% 3.04/0.98      ( ~ m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK2)) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_466]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_4285,plain,
% 3.04/0.98      ( m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK2)) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_5364,plain,
% 3.04/0.98      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK2)) != iProver_top ),
% 3.04/0.98      inference(demodulation,[status(thm)],[c_5208,c_4285]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7760,plain,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_7751,c_5364]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7978,plain,
% 3.04/0.98      ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK2,sK5)) = k1_funct_1(sK5,sK1(sK3,sK2,sK5)) ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_7918,c_7760]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_8438,plain,
% 3.04/0.98      ( m1_subset_1(sK1(sK3,sK2,sK5),sK3) != iProver_top
% 3.04/0.98      | r2_hidden(k1_funct_1(sK5,sK1(sK3,sK2,sK5)),sK2) = iProver_top ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_7978,c_4293]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7765,plain,
% 3.04/0.98      ( r2_hidden(sK1(sK3,sK2,sK5),sK3) = iProver_top ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_6478,c_7760]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_8390,plain,
% 3.04/0.98      ( m1_subset_1(sK1(sK3,sK2,sK5),sK3) = iProver_top ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_7765,c_4299]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_8450,plain,
% 3.04/0.98      ( r2_hidden(k1_funct_1(sK5,sK1(sK3,sK2,sK5)),sK2) = iProver_top ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_8438,c_8390]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_8459,plain,
% 3.04/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.04/0.98      inference(superposition,[status(thm)],[c_8450,c_5897]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(contradiction,plain,
% 3.04/0.98      ( $false ),
% 3.04/0.98      inference(minisat,[status(thm)],[c_8459,c_7751,c_5364]) ).
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.04/0.98  
% 3.04/0.98  ------                               Statistics
% 3.04/0.98  
% 3.04/0.98  ------ General
% 3.04/0.98  
% 3.04/0.98  abstr_ref_over_cycles:                  0
% 3.04/0.98  abstr_ref_under_cycles:                 0
% 3.04/0.98  gc_basic_clause_elim:                   0
% 3.04/0.98  forced_gc_time:                         0
% 3.04/0.98  parsing_time:                           0.018
% 3.04/0.98  unif_index_cands_time:                  0.
% 3.04/0.98  unif_index_add_time:                    0.
% 3.04/0.98  orderings_time:                         0.
% 3.04/0.98  out_proof_time:                         0.012
% 3.04/0.98  total_time:                             0.236
% 3.04/0.98  num_of_symbols:                         56
% 3.04/0.98  num_of_terms:                           5015
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing
% 3.04/0.98  
% 3.04/0.98  num_of_splits:                          3
% 3.04/0.98  num_of_split_atoms:                     3
% 3.04/0.98  num_of_reused_defs:                     0
% 3.04/0.98  num_eq_ax_congr_red:                    12
% 3.04/0.98  num_of_sem_filtered_clauses:            1
% 3.04/0.98  num_of_subtypes:                        0
% 3.04/0.98  monotx_restored_types:                  0
% 3.04/0.98  sat_num_of_epr_types:                   0
% 3.04/0.98  sat_num_of_non_cyclic_types:            0
% 3.04/0.98  sat_guarded_non_collapsed_types:        0
% 3.04/0.98  num_pure_diseq_elim:                    0
% 3.04/0.98  simp_replaced_by:                       0
% 3.04/0.98  res_preprocessed:                       131
% 3.04/0.98  prep_upred:                             0
% 3.04/0.98  prep_unflattend:                        263
% 3.04/0.98  smt_new_axioms:                         0
% 3.04/0.98  pred_elim_cands:                        7
% 3.04/0.98  pred_elim:                              3
% 3.04/0.98  pred_elim_cl:                           -3
% 3.04/0.98  pred_elim_cycles:                       8
% 3.04/0.98  merged_defs:                            2
% 3.04/0.98  merged_defs_ncl:                        0
% 3.04/0.98  bin_hyper_res:                          3
% 3.04/0.98  prep_cycles:                            3
% 3.04/0.98  pred_elim_time:                         0.069
% 3.04/0.98  splitting_time:                         0.
% 3.04/0.98  sem_filter_time:                        0.
% 3.04/0.98  monotx_time:                            0.
% 3.04/0.98  subtype_inf_time:                       0.
% 3.04/0.98  
% 3.04/0.98  ------ Problem properties
% 3.04/0.98  
% 3.04/0.98  clauses:                                36
% 3.04/0.98  conjectures:                            4
% 3.04/0.98  epr:                                    9
% 3.04/0.98  horn:                                   25
% 3.04/0.98  ground:                                 13
% 3.04/0.98  unary:                                  11
% 3.04/0.98  binary:                                 11
% 3.04/0.98  lits:                                   86
% 3.04/0.98  lits_eq:                                24
% 3.04/0.98  fd_pure:                                0
% 3.04/0.98  fd_pseudo:                              0
% 3.04/0.98  fd_cond:                                4
% 3.04/0.98  fd_pseudo_cond:                         0
% 3.04/0.98  ac_symbols:                             0
% 3.04/0.98  
% 3.04/0.98  ------ Propositional Solver
% 3.04/0.98  
% 3.04/0.98  prop_solver_calls:                      24
% 3.04/0.98  prop_fast_solver_calls:                 1702
% 3.04/0.98  smt_solver_calls:                       0
% 3.04/0.98  smt_fast_solver_calls:                  0
% 3.04/0.98  prop_num_of_clauses:                    2174
% 3.04/0.98  prop_preprocess_simplified:             6700
% 3.04/0.98  prop_fo_subsumed:                       66
% 3.04/0.98  prop_solver_time:                       0.
% 3.04/0.98  smt_solver_time:                        0.
% 3.04/0.98  smt_fast_solver_time:                   0.
% 3.04/0.98  prop_fast_solver_time:                  0.
% 3.04/0.98  prop_unsat_core_time:                   0.
% 3.04/0.98  
% 3.04/0.98  ------ QBF
% 3.04/0.98  
% 3.04/0.98  qbf_q_res:                              0
% 3.04/0.98  qbf_num_tautologies:                    0
% 3.04/0.98  qbf_prep_cycles:                        0
% 3.04/0.98  
% 3.04/0.98  ------ BMC1
% 3.04/0.98  
% 3.04/0.98  bmc1_current_bound:                     -1
% 3.04/0.98  bmc1_last_solved_bound:                 -1
% 3.04/0.98  bmc1_unsat_core_size:                   -1
% 3.04/0.98  bmc1_unsat_core_parents_size:           -1
% 3.04/0.98  bmc1_merge_next_fun:                    0
% 3.04/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.04/0.98  
% 3.04/0.98  ------ Instantiation
% 3.04/0.98  
% 3.04/0.98  inst_num_of_clauses:                    622
% 3.04/0.98  inst_num_in_passive:                    91
% 3.04/0.98  inst_num_in_active:                     343
% 3.04/0.98  inst_num_in_unprocessed:                188
% 3.04/0.98  inst_num_of_loops:                      430
% 3.04/0.98  inst_num_of_learning_restarts:          0
% 3.04/0.98  inst_num_moves_active_passive:          84
% 3.04/0.98  inst_lit_activity:                      0
% 3.04/0.98  inst_lit_activity_moves:                0
% 3.04/0.98  inst_num_tautologies:                   0
% 3.04/0.98  inst_num_prop_implied:                  0
% 3.04/0.98  inst_num_existing_simplified:           0
% 3.04/0.98  inst_num_eq_res_simplified:             0
% 3.04/0.98  inst_num_child_elim:                    0
% 3.04/0.98  inst_num_of_dismatching_blockings:      507
% 3.04/0.98  inst_num_of_non_proper_insts:           546
% 3.04/0.98  inst_num_of_duplicates:                 0
% 3.04/0.98  inst_inst_num_from_inst_to_res:         0
% 3.04/0.98  inst_dismatching_checking_time:         0.
% 3.04/0.98  
% 3.04/0.98  ------ Resolution
% 3.04/0.98  
% 3.04/0.98  res_num_of_clauses:                     0
% 3.04/0.98  res_num_in_passive:                     0
% 3.04/0.98  res_num_in_active:                      0
% 3.04/0.98  res_num_of_loops:                       134
% 3.04/0.98  res_forward_subset_subsumed:            42
% 3.04/0.98  res_backward_subset_subsumed:           0
% 3.04/0.98  res_forward_subsumed:                   8
% 3.04/0.98  res_backward_subsumed:                  9
% 3.04/0.98  res_forward_subsumption_resolution:     8
% 3.04/0.98  res_backward_subsumption_resolution:    1
% 3.04/0.98  res_clause_to_clause_subsumption:       414
% 3.04/0.98  res_orphan_elimination:                 0
% 3.04/0.98  res_tautology_del:                      68
% 3.04/0.98  res_num_eq_res_simplified:              0
% 3.04/0.98  res_num_sel_changes:                    0
% 3.04/0.98  res_moves_from_active_to_pass:          0
% 3.04/0.98  
% 3.04/0.98  ------ Superposition
% 3.04/0.98  
% 3.04/0.98  sup_time_total:                         0.
% 3.04/0.98  sup_time_generating:                    0.
% 3.04/0.98  sup_time_sim_full:                      0.
% 3.04/0.98  sup_time_sim_immed:                     0.
% 3.04/0.98  
% 3.04/0.98  sup_num_of_clauses:                     106
% 3.04/0.98  sup_num_in_active:                      77
% 3.04/0.98  sup_num_in_passive:                     29
% 3.04/0.98  sup_num_of_loops:                       85
% 3.04/0.98  sup_fw_superposition:                   27
% 3.04/0.98  sup_bw_superposition:                   93
% 3.04/0.98  sup_immediate_simplified:               29
% 3.04/0.98  sup_given_eliminated:                   0
% 3.04/0.98  comparisons_done:                       0
% 3.04/0.98  comparisons_avoided:                    9
% 3.04/0.98  
% 3.04/0.98  ------ Simplifications
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  sim_fw_subset_subsumed:                 17
% 3.04/0.98  sim_bw_subset_subsumed:                 5
% 3.04/0.98  sim_fw_subsumed:                        4
% 3.04/0.98  sim_bw_subsumed:                        0
% 3.04/0.98  sim_fw_subsumption_res:                 5
% 3.04/0.98  sim_bw_subsumption_res:                 0
% 3.04/0.98  sim_tautology_del:                      2
% 3.04/0.98  sim_eq_tautology_del:                   0
% 3.04/0.98  sim_eq_res_simp:                        0
% 3.04/0.98  sim_fw_demodulated:                     5
% 3.04/0.98  sim_bw_demodulated:                     7
% 3.04/0.98  sim_light_normalised:                   15
% 3.04/0.98  sim_joinable_taut:                      0
% 3.04/0.98  sim_joinable_simp:                      0
% 3.04/0.98  sim_ac_normalised:                      0
% 3.04/0.98  sim_smt_subsumption:                    0
% 3.04/0.98  
%------------------------------------------------------------------------------
