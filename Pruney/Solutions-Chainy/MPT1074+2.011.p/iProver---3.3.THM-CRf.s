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
% DateTime   : Thu Dec  3 12:10:14 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  154 (2492 expanded)
%              Number of clauses        :   90 ( 748 expanded)
%              Number of leaves         :   18 ( 674 expanded)
%              Depth                    :   27
%              Number of atoms          :  490 (15142 expanded)
%              Number of equality atoms :  164 (1781 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1)
        & r2_hidden(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1)
        & r2_hidden(sK1(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f35])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK1(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK1(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f40,plain,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2)
        | ~ m1_subset_1(X4,sK3) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f39,f38,f37])).

fof(f67,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f34,plain,(
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

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2)
      | ~ m1_subset_1(X4,sK3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK1(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | r2_hidden(sK1(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_567,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | r2_hidden(sK1(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_568,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
    | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_4485,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_35,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_569,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4745,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4746,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4745])).

cnf(c_5202,plain,
    ( r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4485,c_35,c_569,c_4746])).

cnf(c_5203,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5202])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4498,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5211,plain,
    ( m1_subset_1(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5203,c_4498])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1369,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_1370,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_1369])).

cnf(c_1372,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1370,c_26])).

cnf(c_4492,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4495,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5363,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4492,c_4495])).

cnf(c_5593,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1372,c_5363])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_13,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_597,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_598,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X0)
    | k3_funct_2(X0,X1,sK5,X2) = k1_funct_1(sK5,X2) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_1358,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | v1_xboole_0(X1)
    | X4 != X3
    | k3_funct_2(X1,X4,sK5,X0) = k1_funct_1(sK5,X0)
    | k1_relset_1(k1_xboole_0,X3,X2) != k1_xboole_0
    | sK5 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_598])).

cnf(c_1359,plain,
    ( ~ m1_subset_1(X0,k1_xboole_0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | v1_xboole_0(k1_xboole_0)
    | k3_funct_2(k1_xboole_0,X1,sK5,X0) = k1_funct_1(sK5,X0)
    | k1_relset_1(k1_xboole_0,X1,sK5) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1358])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_409,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_6])).

cnf(c_410,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_834,plain,
    ( v1_xboole_0(X0)
    | sK0(X0) != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_410])).

cnf(c_835,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_834])).

cnf(c_1361,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1359,c_835])).

cnf(c_1931,plain,
    ( sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1361])).

cnf(c_5707,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5593,c_1931])).

cnf(c_6781,plain,
    ( m1_subset_1(sK1(sK3,X0,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5211,c_5707])).

cnf(c_1450,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,sK5,X0) = k1_funct_1(sK5,X0)
    | sK5 != sK5
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_598])).

cnf(c_1451,plain,
    ( ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_xboole_0(sK3)
    | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_1450])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1455,plain,
    ( ~ m1_subset_1(X0,sK3)
    | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1451,c_30,c_26])).

cnf(c_4477,plain,
    ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_6787,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,X0,sK5)) = k1_funct_1(sK5,sK1(sK3,X0,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6781,c_4477])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4494,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7231,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,X0,sK5)) = k1_funct_1(sK5,sK1(sK3,X0,sK5))
    | k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_6787,c_4494])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4493,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7739,plain,
    ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
    | m1_subset_1(sK1(sK3,X0,sK5),sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7231,c_4493])).

cnf(c_5712,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5707,c_5203])).

cnf(c_6996,plain,
    ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
    | r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5712,c_4494])).

cnf(c_7486,plain,
    ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
    | m1_subset_1(sK1(sK3,X0,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6996,c_4498])).

cnf(c_7940,plain,
    ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
    | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7739,c_7486])).

cnf(c_18,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r2_hidden(k1_funct_1(X0,sK1(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_582,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r2_hidden(k1_funct_1(X0,sK1(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_583,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
    | ~ r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_4484,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_584,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_5193,plain,
    ( r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4484,c_35,c_584,c_4746])).

cnf(c_5194,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5193])).

cnf(c_5713,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5707,c_5194])).

cnf(c_7952,plain,
    ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7940,c_5713])).

cnf(c_8100,plain,
    ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7952,c_4494])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4496,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8101,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8100,c_4496])).

cnf(c_5359,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4492,c_4494])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_239,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_239])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k2_relset_1(sK3,sK4,sK5) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_240,c_24])).

cnf(c_433,plain,
    ( ~ m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_4486,plain,
    ( m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_5480,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5359,c_4486])).

cnf(c_8903,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8101,c_5480])).

cnf(c_8908,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK2,sK5)) = k1_funct_1(sK5,sK1(sK3,sK2,sK5)) ),
    inference(superposition,[status(thm)],[c_6787,c_8903])).

cnf(c_8974,plain,
    ( m1_subset_1(sK1(sK3,sK2,sK5),sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(sK3,sK2,sK5)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8908,c_4493])).

cnf(c_8909,plain,
    ( r2_hidden(sK1(sK3,sK2,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5712,c_8903])).

cnf(c_8918,plain,
    ( m1_subset_1(sK1(sK3,sK2,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_8909,c_4498])).

cnf(c_8986,plain,
    ( r2_hidden(k1_funct_1(sK5,sK1(sK3,sK2,sK5)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8974,c_8918])).

cnf(c_8995,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8986,c_5713])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8995,c_8101,c_5480])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.06/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.01  
% 3.06/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/1.01  
% 3.06/1.01  ------  iProver source info
% 3.06/1.01  
% 3.06/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.06/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/1.01  git: non_committed_changes: false
% 3.06/1.01  git: last_make_outside_of_git: false
% 3.06/1.01  
% 3.06/1.01  ------ 
% 3.06/1.01  
% 3.06/1.01  ------ Input Options
% 3.06/1.01  
% 3.06/1.01  --out_options                           all
% 3.06/1.01  --tptp_safe_out                         true
% 3.06/1.01  --problem_path                          ""
% 3.06/1.01  --include_path                          ""
% 3.06/1.01  --clausifier                            res/vclausify_rel
% 3.06/1.01  --clausifier_options                    --mode clausify
% 3.06/1.01  --stdin                                 false
% 3.06/1.01  --stats_out                             all
% 3.06/1.01  
% 3.06/1.01  ------ General Options
% 3.06/1.01  
% 3.06/1.01  --fof                                   false
% 3.06/1.01  --time_out_real                         305.
% 3.06/1.01  --time_out_virtual                      -1.
% 3.06/1.01  --symbol_type_check                     false
% 3.06/1.01  --clausify_out                          false
% 3.06/1.01  --sig_cnt_out                           false
% 3.06/1.01  --trig_cnt_out                          false
% 3.06/1.01  --trig_cnt_out_tolerance                1.
% 3.06/1.01  --trig_cnt_out_sk_spl                   false
% 3.06/1.01  --abstr_cl_out                          false
% 3.06/1.01  
% 3.06/1.01  ------ Global Options
% 3.06/1.01  
% 3.06/1.01  --schedule                              default
% 3.06/1.01  --add_important_lit                     false
% 3.06/1.01  --prop_solver_per_cl                    1000
% 3.06/1.01  --min_unsat_core                        false
% 3.06/1.01  --soft_assumptions                      false
% 3.06/1.01  --soft_lemma_size                       3
% 3.06/1.01  --prop_impl_unit_size                   0
% 3.06/1.01  --prop_impl_unit                        []
% 3.06/1.01  --share_sel_clauses                     true
% 3.06/1.01  --reset_solvers                         false
% 3.06/1.01  --bc_imp_inh                            [conj_cone]
% 3.06/1.01  --conj_cone_tolerance                   3.
% 3.06/1.01  --extra_neg_conj                        none
% 3.06/1.01  --large_theory_mode                     true
% 3.06/1.01  --prolific_symb_bound                   200
% 3.06/1.01  --lt_threshold                          2000
% 3.06/1.01  --clause_weak_htbl                      true
% 3.06/1.01  --gc_record_bc_elim                     false
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing Options
% 3.06/1.01  
% 3.06/1.01  --preprocessing_flag                    true
% 3.06/1.01  --time_out_prep_mult                    0.1
% 3.06/1.01  --splitting_mode                        input
% 3.06/1.01  --splitting_grd                         true
% 3.06/1.01  --splitting_cvd                         false
% 3.06/1.01  --splitting_cvd_svl                     false
% 3.06/1.01  --splitting_nvd                         32
% 3.06/1.01  --sub_typing                            true
% 3.06/1.01  --prep_gs_sim                           true
% 3.06/1.01  --prep_unflatten                        true
% 3.06/1.01  --prep_res_sim                          true
% 3.06/1.01  --prep_upred                            true
% 3.06/1.01  --prep_sem_filter                       exhaustive
% 3.06/1.01  --prep_sem_filter_out                   false
% 3.06/1.01  --pred_elim                             true
% 3.06/1.01  --res_sim_input                         true
% 3.06/1.01  --eq_ax_congr_red                       true
% 3.06/1.01  --pure_diseq_elim                       true
% 3.06/1.01  --brand_transform                       false
% 3.06/1.01  --non_eq_to_eq                          false
% 3.06/1.01  --prep_def_merge                        true
% 3.06/1.01  --prep_def_merge_prop_impl              false
% 3.06/1.01  --prep_def_merge_mbd                    true
% 3.06/1.01  --prep_def_merge_tr_red                 false
% 3.06/1.01  --prep_def_merge_tr_cl                  false
% 3.06/1.01  --smt_preprocessing                     true
% 3.06/1.01  --smt_ac_axioms                         fast
% 3.06/1.01  --preprocessed_out                      false
% 3.06/1.01  --preprocessed_stats                    false
% 3.06/1.01  
% 3.06/1.01  ------ Abstraction refinement Options
% 3.06/1.01  
% 3.06/1.01  --abstr_ref                             []
% 3.06/1.01  --abstr_ref_prep                        false
% 3.06/1.01  --abstr_ref_until_sat                   false
% 3.06/1.01  --abstr_ref_sig_restrict                funpre
% 3.06/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.01  --abstr_ref_under                       []
% 3.06/1.01  
% 3.06/1.01  ------ SAT Options
% 3.06/1.01  
% 3.06/1.01  --sat_mode                              false
% 3.06/1.01  --sat_fm_restart_options                ""
% 3.06/1.01  --sat_gr_def                            false
% 3.06/1.01  --sat_epr_types                         true
% 3.06/1.01  --sat_non_cyclic_types                  false
% 3.06/1.01  --sat_finite_models                     false
% 3.06/1.01  --sat_fm_lemmas                         false
% 3.06/1.01  --sat_fm_prep                           false
% 3.06/1.01  --sat_fm_uc_incr                        true
% 3.06/1.01  --sat_out_model                         small
% 3.06/1.01  --sat_out_clauses                       false
% 3.06/1.01  
% 3.06/1.01  ------ QBF Options
% 3.06/1.01  
% 3.06/1.01  --qbf_mode                              false
% 3.06/1.01  --qbf_elim_univ                         false
% 3.06/1.01  --qbf_dom_inst                          none
% 3.06/1.01  --qbf_dom_pre_inst                      false
% 3.06/1.01  --qbf_sk_in                             false
% 3.06/1.01  --qbf_pred_elim                         true
% 3.06/1.01  --qbf_split                             512
% 3.06/1.01  
% 3.06/1.01  ------ BMC1 Options
% 3.06/1.01  
% 3.06/1.01  --bmc1_incremental                      false
% 3.06/1.01  --bmc1_axioms                           reachable_all
% 3.06/1.01  --bmc1_min_bound                        0
% 3.06/1.01  --bmc1_max_bound                        -1
% 3.06/1.01  --bmc1_max_bound_default                -1
% 3.06/1.01  --bmc1_symbol_reachability              true
% 3.06/1.01  --bmc1_property_lemmas                  false
% 3.06/1.01  --bmc1_k_induction                      false
% 3.06/1.01  --bmc1_non_equiv_states                 false
% 3.06/1.01  --bmc1_deadlock                         false
% 3.06/1.01  --bmc1_ucm                              false
% 3.06/1.01  --bmc1_add_unsat_core                   none
% 3.06/1.01  --bmc1_unsat_core_children              false
% 3.06/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.01  --bmc1_out_stat                         full
% 3.06/1.01  --bmc1_ground_init                      false
% 3.06/1.01  --bmc1_pre_inst_next_state              false
% 3.06/1.01  --bmc1_pre_inst_state                   false
% 3.06/1.01  --bmc1_pre_inst_reach_state             false
% 3.06/1.01  --bmc1_out_unsat_core                   false
% 3.06/1.01  --bmc1_aig_witness_out                  false
% 3.06/1.01  --bmc1_verbose                          false
% 3.06/1.01  --bmc1_dump_clauses_tptp                false
% 3.06/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.01  --bmc1_dump_file                        -
% 3.06/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.01  --bmc1_ucm_extend_mode                  1
% 3.06/1.01  --bmc1_ucm_init_mode                    2
% 3.06/1.01  --bmc1_ucm_cone_mode                    none
% 3.06/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.01  --bmc1_ucm_relax_model                  4
% 3.06/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.01  --bmc1_ucm_layered_model                none
% 3.06/1.01  --bmc1_ucm_max_lemma_size               10
% 3.06/1.01  
% 3.06/1.01  ------ AIG Options
% 3.06/1.01  
% 3.06/1.01  --aig_mode                              false
% 3.06/1.01  
% 3.06/1.01  ------ Instantiation Options
% 3.06/1.01  
% 3.06/1.01  --instantiation_flag                    true
% 3.06/1.01  --inst_sos_flag                         false
% 3.06/1.01  --inst_sos_phase                        true
% 3.06/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.01  --inst_lit_sel_side                     num_symb
% 3.06/1.01  --inst_solver_per_active                1400
% 3.06/1.01  --inst_solver_calls_frac                1.
% 3.06/1.01  --inst_passive_queue_type               priority_queues
% 3.06/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.01  --inst_passive_queues_freq              [25;2]
% 3.06/1.01  --inst_dismatching                      true
% 3.06/1.01  --inst_eager_unprocessed_to_passive     true
% 3.06/1.01  --inst_prop_sim_given                   true
% 3.06/1.01  --inst_prop_sim_new                     false
% 3.06/1.01  --inst_subs_new                         false
% 3.06/1.01  --inst_eq_res_simp                      false
% 3.06/1.01  --inst_subs_given                       false
% 3.06/1.01  --inst_orphan_elimination               true
% 3.06/1.01  --inst_learning_loop_flag               true
% 3.06/1.01  --inst_learning_start                   3000
% 3.06/1.01  --inst_learning_factor                  2
% 3.06/1.01  --inst_start_prop_sim_after_learn       3
% 3.06/1.01  --inst_sel_renew                        solver
% 3.06/1.01  --inst_lit_activity_flag                true
% 3.06/1.01  --inst_restr_to_given                   false
% 3.06/1.01  --inst_activity_threshold               500
% 3.06/1.01  --inst_out_proof                        true
% 3.06/1.01  
% 3.06/1.01  ------ Resolution Options
% 3.06/1.01  
% 3.06/1.01  --resolution_flag                       true
% 3.06/1.01  --res_lit_sel                           adaptive
% 3.06/1.01  --res_lit_sel_side                      none
% 3.06/1.01  --res_ordering                          kbo
% 3.06/1.01  --res_to_prop_solver                    active
% 3.06/1.01  --res_prop_simpl_new                    false
% 3.06/1.01  --res_prop_simpl_given                  true
% 3.06/1.01  --res_passive_queue_type                priority_queues
% 3.06/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.01  --res_passive_queues_freq               [15;5]
% 3.06/1.01  --res_forward_subs                      full
% 3.06/1.01  --res_backward_subs                     full
% 3.06/1.01  --res_forward_subs_resolution           true
% 3.06/1.01  --res_backward_subs_resolution          true
% 3.06/1.01  --res_orphan_elimination                true
% 3.06/1.01  --res_time_limit                        2.
% 3.06/1.01  --res_out_proof                         true
% 3.06/1.01  
% 3.06/1.01  ------ Superposition Options
% 3.06/1.01  
% 3.06/1.01  --superposition_flag                    true
% 3.06/1.01  --sup_passive_queue_type                priority_queues
% 3.06/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.01  --demod_completeness_check              fast
% 3.06/1.01  --demod_use_ground                      true
% 3.06/1.01  --sup_to_prop_solver                    passive
% 3.06/1.01  --sup_prop_simpl_new                    true
% 3.06/1.01  --sup_prop_simpl_given                  true
% 3.06/1.01  --sup_fun_splitting                     false
% 3.06/1.01  --sup_smt_interval                      50000
% 3.06/1.01  
% 3.06/1.01  ------ Superposition Simplification Setup
% 3.06/1.01  
% 3.06/1.01  --sup_indices_passive                   []
% 3.06/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.01  --sup_full_bw                           [BwDemod]
% 3.06/1.01  --sup_immed_triv                        [TrivRules]
% 3.06/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.01  --sup_immed_bw_main                     []
% 3.06/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.01  
% 3.06/1.01  ------ Combination Options
% 3.06/1.01  
% 3.06/1.01  --comb_res_mult                         3
% 3.06/1.01  --comb_sup_mult                         2
% 3.06/1.01  --comb_inst_mult                        10
% 3.06/1.01  
% 3.06/1.01  ------ Debug Options
% 3.06/1.01  
% 3.06/1.01  --dbg_backtrace                         false
% 3.06/1.01  --dbg_dump_prop_clauses                 false
% 3.06/1.01  --dbg_dump_prop_clauses_file            -
% 3.06/1.01  --dbg_out_stat                          false
% 3.06/1.01  ------ Parsing...
% 3.06/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/1.01  ------ Proving...
% 3.06/1.01  ------ Problem Properties 
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  clauses                                 33
% 3.06/1.01  conjectures                             4
% 3.06/1.01  EPR                                     8
% 3.06/1.01  Horn                                    22
% 3.06/1.01  unary                                   10
% 3.06/1.01  binary                                  11
% 3.06/1.01  lits                                    79
% 3.06/1.01  lits eq                                 24
% 3.06/1.01  fd_pure                                 0
% 3.06/1.01  fd_pseudo                               0
% 3.06/1.01  fd_cond                                 4
% 3.06/1.01  fd_pseudo_cond                          0
% 3.06/1.01  AC symbols                              0
% 3.06/1.01  
% 3.06/1.01  ------ Schedule dynamic 5 is on 
% 3.06/1.01  
% 3.06/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  ------ 
% 3.06/1.01  Current options:
% 3.06/1.01  ------ 
% 3.06/1.01  
% 3.06/1.01  ------ Input Options
% 3.06/1.01  
% 3.06/1.01  --out_options                           all
% 3.06/1.01  --tptp_safe_out                         true
% 3.06/1.01  --problem_path                          ""
% 3.06/1.01  --include_path                          ""
% 3.06/1.01  --clausifier                            res/vclausify_rel
% 3.06/1.01  --clausifier_options                    --mode clausify
% 3.06/1.01  --stdin                                 false
% 3.06/1.01  --stats_out                             all
% 3.06/1.01  
% 3.06/1.01  ------ General Options
% 3.06/1.01  
% 3.06/1.01  --fof                                   false
% 3.06/1.01  --time_out_real                         305.
% 3.06/1.01  --time_out_virtual                      -1.
% 3.06/1.01  --symbol_type_check                     false
% 3.06/1.01  --clausify_out                          false
% 3.06/1.01  --sig_cnt_out                           false
% 3.06/1.01  --trig_cnt_out                          false
% 3.06/1.01  --trig_cnt_out_tolerance                1.
% 3.06/1.01  --trig_cnt_out_sk_spl                   false
% 3.06/1.01  --abstr_cl_out                          false
% 3.06/1.01  
% 3.06/1.01  ------ Global Options
% 3.06/1.01  
% 3.06/1.01  --schedule                              default
% 3.06/1.01  --add_important_lit                     false
% 3.06/1.01  --prop_solver_per_cl                    1000
% 3.06/1.01  --min_unsat_core                        false
% 3.06/1.01  --soft_assumptions                      false
% 3.06/1.01  --soft_lemma_size                       3
% 3.06/1.01  --prop_impl_unit_size                   0
% 3.06/1.01  --prop_impl_unit                        []
% 3.06/1.01  --share_sel_clauses                     true
% 3.06/1.01  --reset_solvers                         false
% 3.06/1.01  --bc_imp_inh                            [conj_cone]
% 3.06/1.01  --conj_cone_tolerance                   3.
% 3.06/1.01  --extra_neg_conj                        none
% 3.06/1.01  --large_theory_mode                     true
% 3.06/1.01  --prolific_symb_bound                   200
% 3.06/1.01  --lt_threshold                          2000
% 3.06/1.01  --clause_weak_htbl                      true
% 3.06/1.01  --gc_record_bc_elim                     false
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing Options
% 3.06/1.01  
% 3.06/1.01  --preprocessing_flag                    true
% 3.06/1.01  --time_out_prep_mult                    0.1
% 3.06/1.01  --splitting_mode                        input
% 3.06/1.01  --splitting_grd                         true
% 3.06/1.01  --splitting_cvd                         false
% 3.06/1.01  --splitting_cvd_svl                     false
% 3.06/1.01  --splitting_nvd                         32
% 3.06/1.01  --sub_typing                            true
% 3.06/1.01  --prep_gs_sim                           true
% 3.06/1.01  --prep_unflatten                        true
% 3.06/1.01  --prep_res_sim                          true
% 3.06/1.01  --prep_upred                            true
% 3.06/1.01  --prep_sem_filter                       exhaustive
% 3.06/1.01  --prep_sem_filter_out                   false
% 3.06/1.01  --pred_elim                             true
% 3.06/1.01  --res_sim_input                         true
% 3.06/1.01  --eq_ax_congr_red                       true
% 3.06/1.01  --pure_diseq_elim                       true
% 3.06/1.01  --brand_transform                       false
% 3.06/1.01  --non_eq_to_eq                          false
% 3.06/1.01  --prep_def_merge                        true
% 3.06/1.01  --prep_def_merge_prop_impl              false
% 3.06/1.01  --prep_def_merge_mbd                    true
% 3.06/1.01  --prep_def_merge_tr_red                 false
% 3.06/1.01  --prep_def_merge_tr_cl                  false
% 3.06/1.01  --smt_preprocessing                     true
% 3.06/1.01  --smt_ac_axioms                         fast
% 3.06/1.01  --preprocessed_out                      false
% 3.06/1.01  --preprocessed_stats                    false
% 3.06/1.01  
% 3.06/1.01  ------ Abstraction refinement Options
% 3.06/1.01  
% 3.06/1.01  --abstr_ref                             []
% 3.06/1.01  --abstr_ref_prep                        false
% 3.06/1.01  --abstr_ref_until_sat                   false
% 3.06/1.01  --abstr_ref_sig_restrict                funpre
% 3.06/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.01  --abstr_ref_under                       []
% 3.06/1.01  
% 3.06/1.01  ------ SAT Options
% 3.06/1.01  
% 3.06/1.01  --sat_mode                              false
% 3.06/1.01  --sat_fm_restart_options                ""
% 3.06/1.01  --sat_gr_def                            false
% 3.06/1.01  --sat_epr_types                         true
% 3.06/1.01  --sat_non_cyclic_types                  false
% 3.06/1.01  --sat_finite_models                     false
% 3.06/1.01  --sat_fm_lemmas                         false
% 3.06/1.01  --sat_fm_prep                           false
% 3.06/1.01  --sat_fm_uc_incr                        true
% 3.06/1.01  --sat_out_model                         small
% 3.06/1.01  --sat_out_clauses                       false
% 3.06/1.01  
% 3.06/1.01  ------ QBF Options
% 3.06/1.01  
% 3.06/1.01  --qbf_mode                              false
% 3.06/1.01  --qbf_elim_univ                         false
% 3.06/1.01  --qbf_dom_inst                          none
% 3.06/1.01  --qbf_dom_pre_inst                      false
% 3.06/1.01  --qbf_sk_in                             false
% 3.06/1.01  --qbf_pred_elim                         true
% 3.06/1.01  --qbf_split                             512
% 3.06/1.01  
% 3.06/1.01  ------ BMC1 Options
% 3.06/1.01  
% 3.06/1.01  --bmc1_incremental                      false
% 3.06/1.01  --bmc1_axioms                           reachable_all
% 3.06/1.01  --bmc1_min_bound                        0
% 3.06/1.01  --bmc1_max_bound                        -1
% 3.06/1.01  --bmc1_max_bound_default                -1
% 3.06/1.01  --bmc1_symbol_reachability              true
% 3.06/1.01  --bmc1_property_lemmas                  false
% 3.06/1.01  --bmc1_k_induction                      false
% 3.06/1.01  --bmc1_non_equiv_states                 false
% 3.06/1.01  --bmc1_deadlock                         false
% 3.06/1.01  --bmc1_ucm                              false
% 3.06/1.01  --bmc1_add_unsat_core                   none
% 3.06/1.01  --bmc1_unsat_core_children              false
% 3.06/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.01  --bmc1_out_stat                         full
% 3.06/1.01  --bmc1_ground_init                      false
% 3.06/1.01  --bmc1_pre_inst_next_state              false
% 3.06/1.01  --bmc1_pre_inst_state                   false
% 3.06/1.01  --bmc1_pre_inst_reach_state             false
% 3.06/1.01  --bmc1_out_unsat_core                   false
% 3.06/1.01  --bmc1_aig_witness_out                  false
% 3.06/1.01  --bmc1_verbose                          false
% 3.06/1.01  --bmc1_dump_clauses_tptp                false
% 3.06/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.01  --bmc1_dump_file                        -
% 3.06/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.01  --bmc1_ucm_extend_mode                  1
% 3.06/1.01  --bmc1_ucm_init_mode                    2
% 3.06/1.01  --bmc1_ucm_cone_mode                    none
% 3.06/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.01  --bmc1_ucm_relax_model                  4
% 3.06/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.01  --bmc1_ucm_layered_model                none
% 3.06/1.01  --bmc1_ucm_max_lemma_size               10
% 3.06/1.01  
% 3.06/1.01  ------ AIG Options
% 3.06/1.01  
% 3.06/1.01  --aig_mode                              false
% 3.06/1.01  
% 3.06/1.01  ------ Instantiation Options
% 3.06/1.01  
% 3.06/1.01  --instantiation_flag                    true
% 3.06/1.01  --inst_sos_flag                         false
% 3.06/1.01  --inst_sos_phase                        true
% 3.06/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.01  --inst_lit_sel_side                     none
% 3.06/1.01  --inst_solver_per_active                1400
% 3.06/1.01  --inst_solver_calls_frac                1.
% 3.06/1.01  --inst_passive_queue_type               priority_queues
% 3.06/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.01  --inst_passive_queues_freq              [25;2]
% 3.06/1.01  --inst_dismatching                      true
% 3.06/1.01  --inst_eager_unprocessed_to_passive     true
% 3.06/1.01  --inst_prop_sim_given                   true
% 3.06/1.01  --inst_prop_sim_new                     false
% 3.06/1.01  --inst_subs_new                         false
% 3.06/1.01  --inst_eq_res_simp                      false
% 3.06/1.01  --inst_subs_given                       false
% 3.06/1.01  --inst_orphan_elimination               true
% 3.06/1.01  --inst_learning_loop_flag               true
% 3.06/1.01  --inst_learning_start                   3000
% 3.06/1.01  --inst_learning_factor                  2
% 3.06/1.01  --inst_start_prop_sim_after_learn       3
% 3.06/1.01  --inst_sel_renew                        solver
% 3.06/1.01  --inst_lit_activity_flag                true
% 3.06/1.01  --inst_restr_to_given                   false
% 3.06/1.01  --inst_activity_threshold               500
% 3.06/1.01  --inst_out_proof                        true
% 3.06/1.01  
% 3.06/1.01  ------ Resolution Options
% 3.06/1.01  
% 3.06/1.01  --resolution_flag                       false
% 3.06/1.01  --res_lit_sel                           adaptive
% 3.06/1.01  --res_lit_sel_side                      none
% 3.06/1.01  --res_ordering                          kbo
% 3.06/1.01  --res_to_prop_solver                    active
% 3.06/1.01  --res_prop_simpl_new                    false
% 3.06/1.01  --res_prop_simpl_given                  true
% 3.06/1.01  --res_passive_queue_type                priority_queues
% 3.06/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.01  --res_passive_queues_freq               [15;5]
% 3.06/1.01  --res_forward_subs                      full
% 3.06/1.01  --res_backward_subs                     full
% 3.06/1.01  --res_forward_subs_resolution           true
% 3.06/1.01  --res_backward_subs_resolution          true
% 3.06/1.01  --res_orphan_elimination                true
% 3.06/1.01  --res_time_limit                        2.
% 3.06/1.01  --res_out_proof                         true
% 3.06/1.01  
% 3.06/1.01  ------ Superposition Options
% 3.06/1.01  
% 3.06/1.01  --superposition_flag                    true
% 3.06/1.01  --sup_passive_queue_type                priority_queues
% 3.06/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.01  --demod_completeness_check              fast
% 3.06/1.01  --demod_use_ground                      true
% 3.06/1.01  --sup_to_prop_solver                    passive
% 3.06/1.01  --sup_prop_simpl_new                    true
% 3.06/1.01  --sup_prop_simpl_given                  true
% 3.06/1.01  --sup_fun_splitting                     false
% 3.06/1.01  --sup_smt_interval                      50000
% 3.06/1.01  
% 3.06/1.01  ------ Superposition Simplification Setup
% 3.06/1.01  
% 3.06/1.01  --sup_indices_passive                   []
% 3.06/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.01  --sup_full_bw                           [BwDemod]
% 3.06/1.01  --sup_immed_triv                        [TrivRules]
% 3.06/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.01  --sup_immed_bw_main                     []
% 3.06/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.01  
% 3.06/1.01  ------ Combination Options
% 3.06/1.01  
% 3.06/1.01  --comb_res_mult                         3
% 3.06/1.01  --comb_sup_mult                         2
% 3.06/1.01  --comb_inst_mult                        10
% 3.06/1.01  
% 3.06/1.01  ------ Debug Options
% 3.06/1.01  
% 3.06/1.01  --dbg_backtrace                         false
% 3.06/1.01  --dbg_dump_prop_clauses                 false
% 3.06/1.01  --dbg_dump_prop_clauses_file            -
% 3.06/1.01  --dbg_out_stat                          false
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  ------ Proving...
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  % SZS status Theorem for theBenchmark.p
% 3.06/1.01  
% 3.06/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/1.01  
% 3.06/1.01  fof(f12,axiom,(
% 3.06/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f25,plain,(
% 3.06/1.01    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.06/1.01    inference(ennf_transformation,[],[f12])).
% 3.06/1.01  
% 3.06/1.01  fof(f26,plain,(
% 3.06/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.06/1.01    inference(flattening,[],[f25])).
% 3.06/1.01  
% 3.06/1.01  fof(f35,plain,(
% 3.06/1.01    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),X0)))),
% 3.06/1.01    introduced(choice_axiom,[])).
% 3.06/1.01  
% 3.06/1.01  fof(f36,plain,(
% 3.06/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.06/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f35])).
% 3.06/1.01  
% 3.06/1.01  fof(f63,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK1(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f36])).
% 3.06/1.01  
% 3.06/1.01  fof(f78,plain,(
% 3.06/1.01    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK1(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.06/1.01    inference(equality_resolution,[],[f63])).
% 3.06/1.01  
% 3.06/1.01  fof(f13,conjecture,(
% 3.06/1.01    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f14,negated_conjecture,(
% 3.06/1.01    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.06/1.01    inference(negated_conjecture,[],[f13])).
% 3.06/1.01  
% 3.06/1.01  fof(f27,plain,(
% 3.06/1.01    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.06/1.01    inference(ennf_transformation,[],[f14])).
% 3.06/1.01  
% 3.06/1.01  fof(f28,plain,(
% 3.06/1.01    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.06/1.01    inference(flattening,[],[f27])).
% 3.06/1.01  
% 3.06/1.01  fof(f39,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK5),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK5,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 3.06/1.01    introduced(choice_axiom,[])).
% 3.06/1.01  
% 3.06/1.01  fof(f38,plain,(
% 3.06/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK4,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK4,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK4))) & v1_funct_2(X3,X1,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))) )),
% 3.06/1.01    introduced(choice_axiom,[])).
% 3.06/1.01  
% 3.06/1.01  fof(f37,plain,(
% 3.06/1.01    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK3,X2,X3),sK2) & ! [X4] : (r2_hidden(k3_funct_2(sK3,X2,X3,X4),sK2) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X2))) & v1_funct_2(X3,sK3,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))),
% 3.06/1.01    introduced(choice_axiom,[])).
% 3.06/1.01  
% 3.06/1.01  fof(f40,plain,(
% 3.06/1.01    ((~r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) & ! [X4] : (r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)),
% 3.06/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f39,f38,f37])).
% 3.06/1.01  
% 3.06/1.01  fof(f67,plain,(
% 3.06/1.01    v1_funct_1(sK5)),
% 3.06/1.01    inference(cnf_transformation,[],[f40])).
% 3.06/1.01  
% 3.06/1.01  fof(f69,plain,(
% 3.06/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.06/1.01    inference(cnf_transformation,[],[f40])).
% 3.06/1.01  
% 3.06/1.01  fof(f6,axiom,(
% 3.06/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f17,plain,(
% 3.06/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.01    inference(ennf_transformation,[],[f6])).
% 3.06/1.01  
% 3.06/1.01  fof(f48,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f17])).
% 3.06/1.01  
% 3.06/1.01  fof(f3,axiom,(
% 3.06/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f15,plain,(
% 3.06/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.06/1.01    inference(ennf_transformation,[],[f3])).
% 3.06/1.01  
% 3.06/1.01  fof(f44,plain,(
% 3.06/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f15])).
% 3.06/1.01  
% 3.06/1.01  fof(f10,axiom,(
% 3.06/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f21,plain,(
% 3.06/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.01    inference(ennf_transformation,[],[f10])).
% 3.06/1.01  
% 3.06/1.01  fof(f22,plain,(
% 3.06/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.01    inference(flattening,[],[f21])).
% 3.06/1.01  
% 3.06/1.01  fof(f34,plain,(
% 3.06/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.01    inference(nnf_transformation,[],[f22])).
% 3.06/1.01  
% 3.06/1.01  fof(f52,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f34])).
% 3.06/1.01  
% 3.06/1.01  fof(f68,plain,(
% 3.06/1.01    v1_funct_2(sK5,sK3,sK4)),
% 3.06/1.01    inference(cnf_transformation,[],[f40])).
% 3.06/1.01  
% 3.06/1.01  fof(f8,axiom,(
% 3.06/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f19,plain,(
% 3.06/1.01    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.01    inference(ennf_transformation,[],[f8])).
% 3.06/1.01  
% 3.06/1.01  fof(f50,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f19])).
% 3.06/1.01  
% 3.06/1.01  fof(f66,plain,(
% 3.06/1.01    ~v1_xboole_0(sK4)),
% 3.06/1.01    inference(cnf_transformation,[],[f40])).
% 3.06/1.01  
% 3.06/1.01  fof(f55,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f34])).
% 3.06/1.01  
% 3.06/1.01  fof(f75,plain,(
% 3.06/1.01    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.06/1.01    inference(equality_resolution,[],[f55])).
% 3.06/1.01  
% 3.06/1.01  fof(f11,axiom,(
% 3.06/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f23,plain,(
% 3.06/1.01    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.06/1.01    inference(ennf_transformation,[],[f11])).
% 3.06/1.01  
% 3.06/1.01  fof(f24,plain,(
% 3.06/1.01    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.06/1.01    inference(flattening,[],[f23])).
% 3.06/1.01  
% 3.06/1.01  fof(f58,plain,(
% 3.06/1.01    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f24])).
% 3.06/1.01  
% 3.06/1.01  fof(f1,axiom,(
% 3.06/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f29,plain,(
% 3.06/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.06/1.01    inference(nnf_transformation,[],[f1])).
% 3.06/1.01  
% 3.06/1.01  fof(f30,plain,(
% 3.06/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.06/1.01    inference(rectify,[],[f29])).
% 3.06/1.01  
% 3.06/1.01  fof(f31,plain,(
% 3.06/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.06/1.01    introduced(choice_axiom,[])).
% 3.06/1.01  
% 3.06/1.01  fof(f32,plain,(
% 3.06/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.06/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.06/1.01  
% 3.06/1.01  fof(f42,plain,(
% 3.06/1.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f32])).
% 3.06/1.01  
% 3.06/1.01  fof(f2,axiom,(
% 3.06/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f43,plain,(
% 3.06/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f2])).
% 3.06/1.01  
% 3.06/1.01  fof(f5,axiom,(
% 3.06/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f16,plain,(
% 3.06/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.06/1.01    inference(ennf_transformation,[],[f5])).
% 3.06/1.01  
% 3.06/1.01  fof(f47,plain,(
% 3.06/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f16])).
% 3.06/1.01  
% 3.06/1.01  fof(f65,plain,(
% 3.06/1.01    ~v1_xboole_0(sK3)),
% 3.06/1.01    inference(cnf_transformation,[],[f40])).
% 3.06/1.01  
% 3.06/1.01  fof(f9,axiom,(
% 3.06/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f20,plain,(
% 3.06/1.01    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.01    inference(ennf_transformation,[],[f9])).
% 3.06/1.01  
% 3.06/1.01  fof(f51,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f20])).
% 3.06/1.01  
% 3.06/1.01  fof(f70,plain,(
% 3.06/1.01    ( ! [X4] : (r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2) | ~m1_subset_1(X4,sK3)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f40])).
% 3.06/1.01  
% 3.06/1.01  fof(f64,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.06/1.01    inference(cnf_transformation,[],[f36])).
% 3.06/1.01  
% 3.06/1.01  fof(f77,plain,(
% 3.06/1.01    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK1(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.06/1.01    inference(equality_resolution,[],[f64])).
% 3.06/1.01  
% 3.06/1.01  fof(f7,axiom,(
% 3.06/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f18,plain,(
% 3.06/1.01    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.01    inference(ennf_transformation,[],[f7])).
% 3.06/1.01  
% 3.06/1.01  fof(f49,plain,(
% 3.06/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f18])).
% 3.06/1.01  
% 3.06/1.01  fof(f4,axiom,(
% 3.06/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.01  
% 3.06/1.01  fof(f33,plain,(
% 3.06/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.06/1.01    inference(nnf_transformation,[],[f4])).
% 3.06/1.01  
% 3.06/1.01  fof(f45,plain,(
% 3.06/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.06/1.01    inference(cnf_transformation,[],[f33])).
% 3.06/1.01  
% 3.06/1.01  fof(f71,plain,(
% 3.06/1.01    ~r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2)),
% 3.06/1.01    inference(cnf_transformation,[],[f40])).
% 3.06/1.01  
% 3.06/1.01  cnf(c_19,plain,
% 3.06/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.06/1.01      | r2_hidden(sK1(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.06/1.01      | ~ v1_funct_1(X0)
% 3.06/1.01      | ~ v1_relat_1(X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_28,negated_conjecture,
% 3.06/1.01      ( v1_funct_1(sK5) ),
% 3.06/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_567,plain,
% 3.06/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.06/1.01      | r2_hidden(sK1(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.06/1.01      | ~ v1_relat_1(X0)
% 3.06/1.01      | sK5 != X0 ),
% 3.06/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_568,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
% 3.06/1.01      | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5))
% 3.06/1.01      | ~ v1_relat_1(sK5) ),
% 3.06/1.01      inference(unflattening,[status(thm)],[c_567]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4485,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.06/1.01      | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
% 3.06/1.01      | v1_relat_1(sK5) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_26,negated_conjecture,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.06/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_35,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_569,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.06/1.01      | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
% 3.06/1.01      | v1_relat_1(sK5) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_7,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.01      | v1_relat_1(X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4745,plain,
% 3.06/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.06/1.01      | v1_relat_1(sK5) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4746,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.06/1.01      | v1_relat_1(sK5) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_4745]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5202,plain,
% 3.06/1.01      ( r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
% 3.06/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_4485,c_35,c_569,c_4746]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5203,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.06/1.01      | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top ),
% 3.06/1.01      inference(renaming,[status(thm)],[c_5202]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3,plain,
% 3.06/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.06/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4498,plain,
% 3.06/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 3.06/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5211,plain,
% 3.06/1.01      ( m1_subset_1(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
% 3.06/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_5203,c_4498]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_16,plain,
% 3.06/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.06/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.06/1.01      | k1_xboole_0 = X2 ),
% 3.06/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_27,negated_conjecture,
% 3.06/1.01      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.06/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1369,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.06/1.01      | sK5 != X0
% 3.06/1.01      | sK4 != X2
% 3.06/1.01      | sK3 != X1
% 3.06/1.01      | k1_xboole_0 = X2 ),
% 3.06/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1370,plain,
% 3.06/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.06/1.01      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.06/1.01      | k1_xboole_0 = sK4 ),
% 3.06/1.01      inference(unflattening,[status(thm)],[c_1369]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1372,plain,
% 3.06/1.01      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_1370,c_26]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4492,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_9,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4495,plain,
% 3.06/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.06/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5363,plain,
% 3.06/1.01      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_4492,c_4495]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5593,plain,
% 3.06/1.01      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_1372,c_5363]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_29,negated_conjecture,
% 3.06/1.01      ( ~ v1_xboole_0(sK4) ),
% 3.06/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_13,plain,
% 3.06/1.01      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.06/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.06/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.06/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_17,plain,
% 3.06/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.06/1.01      | ~ m1_subset_1(X3,X1)
% 3.06/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.01      | ~ v1_funct_1(X0)
% 3.06/1.01      | v1_xboole_0(X1)
% 3.06/1.01      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.06/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_597,plain,
% 3.06/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.06/1.01      | ~ m1_subset_1(X3,X1)
% 3.06/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.01      | v1_xboole_0(X1)
% 3.06/1.01      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 3.06/1.01      | sK5 != X0 ),
% 3.06/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_598,plain,
% 3.06/1.01      ( ~ v1_funct_2(sK5,X0,X1)
% 3.06/1.01      | ~ m1_subset_1(X2,X0)
% 3.06/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/1.01      | v1_xboole_0(X0)
% 3.06/1.01      | k3_funct_2(X0,X1,sK5,X2) = k1_funct_1(sK5,X2) ),
% 3.06/1.01      inference(unflattening,[status(thm)],[c_597]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1358,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,X1)
% 3.06/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
% 3.06/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 3.06/1.01      | v1_xboole_0(X1)
% 3.06/1.01      | X4 != X3
% 3.06/1.01      | k3_funct_2(X1,X4,sK5,X0) = k1_funct_1(sK5,X0)
% 3.06/1.01      | k1_relset_1(k1_xboole_0,X3,X2) != k1_xboole_0
% 3.06/1.01      | sK5 != X2
% 3.06/1.01      | k1_xboole_0 != X1 ),
% 3.06/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_598]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1359,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,k1_xboole_0)
% 3.06/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.06/1.01      | v1_xboole_0(k1_xboole_0)
% 3.06/1.01      | k3_funct_2(k1_xboole_0,X1,sK5,X0) = k1_funct_1(sK5,X0)
% 3.06/1.01      | k1_relset_1(k1_xboole_0,X1,sK5) != k1_xboole_0 ),
% 3.06/1.01      inference(unflattening,[status(thm)],[c_1358]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_0,plain,
% 3.06/1.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2,plain,
% 3.06/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_6,plain,
% 3.06/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_409,plain,
% 3.06/1.01      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.06/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_6]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_410,plain,
% 3.06/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.06/1.01      inference(unflattening,[status(thm)],[c_409]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_834,plain,
% 3.06/1.01      ( v1_xboole_0(X0) | sK0(X0) != X1 | k1_xboole_0 != X0 ),
% 3.06/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_410]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_835,plain,
% 3.06/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.06/1.01      inference(unflattening,[status(thm)],[c_834]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1361,plain,
% 3.06/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_1359,c_835]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1931,plain,
% 3.06/1.01      ( sK4 != k1_xboole_0 ),
% 3.06/1.01      inference(resolution_lifted,[status(thm)],[c_29,c_1361]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5707,plain,
% 3.06/1.01      ( k1_relat_1(sK5) = sK3 ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_5593,c_1931]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_6781,plain,
% 3.06/1.01      ( m1_subset_1(sK1(sK3,X0,sK5),sK3) = iProver_top
% 3.06/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
% 3.06/1.01      inference(light_normalisation,[status(thm)],[c_5211,c_5707]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1450,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,X1)
% 3.06/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.01      | v1_xboole_0(X1)
% 3.06/1.01      | k3_funct_2(X1,X2,sK5,X0) = k1_funct_1(sK5,X0)
% 3.06/1.01      | sK5 != sK5
% 3.06/1.01      | sK4 != X2
% 3.06/1.01      | sK3 != X1 ),
% 3.06/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_598]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1451,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,sK3)
% 3.06/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.06/1.01      | v1_xboole_0(sK3)
% 3.06/1.01      | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
% 3.06/1.01      inference(unflattening,[status(thm)],[c_1450]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_30,negated_conjecture,
% 3.06/1.01      ( ~ v1_xboole_0(sK3) ),
% 3.06/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1455,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,sK3)
% 3.06/1.01      | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_1451,c_30,c_26]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4477,plain,
% 3.06/1.01      ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
% 3.06/1.01      | m1_subset_1(X0,sK3) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_1455]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_6787,plain,
% 3.06/1.01      ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,X0,sK5)) = k1_funct_1(sK5,sK1(sK3,X0,sK5))
% 3.06/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_6781,c_4477]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_10,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4494,plain,
% 3.06/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.06/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_7231,plain,
% 3.06/1.01      ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,X0,sK5)) = k1_funct_1(sK5,sK1(sK3,X0,sK5))
% 3.06/1.01      | k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5) ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_6787,c_4494]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_25,negated_conjecture,
% 3.06/1.01      ( ~ m1_subset_1(X0,sK3)
% 3.06/1.01      | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) ),
% 3.06/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4493,plain,
% 3.06/1.01      ( m1_subset_1(X0,sK3) != iProver_top
% 3.06/1.01      | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_7739,plain,
% 3.06/1.01      ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
% 3.06/1.01      | m1_subset_1(sK1(sK3,X0,sK5),sK3) != iProver_top
% 3.06/1.01      | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),sK2) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_7231,c_4493]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5712,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.06/1.01      | r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top ),
% 3.06/1.01      inference(demodulation,[status(thm)],[c_5707,c_5203]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_6996,plain,
% 3.06/1.01      ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
% 3.06/1.01      | r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_5712,c_4494]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_7486,plain,
% 3.06/1.01      ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
% 3.06/1.01      | m1_subset_1(sK1(sK3,X0,sK5),sK3) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_6996,c_4498]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_7940,plain,
% 3.06/1.01      ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
% 3.06/1.01      | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),sK2) = iProver_top ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_7739,c_7486]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_18,plain,
% 3.06/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.06/1.01      | ~ r2_hidden(k1_funct_1(X0,sK1(k1_relat_1(X0),X1,X0)),X1)
% 3.06/1.01      | ~ v1_funct_1(X0)
% 3.06/1.01      | ~ v1_relat_1(X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_582,plain,
% 3.06/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.06/1.01      | ~ r2_hidden(k1_funct_1(X0,sK1(k1_relat_1(X0),X1,X0)),X1)
% 3.06/1.01      | ~ v1_relat_1(X0)
% 3.06/1.01      | sK5 != X0 ),
% 3.06/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_583,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
% 3.06/1.01      | ~ r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0)
% 3.06/1.01      | ~ v1_relat_1(sK5) ),
% 3.06/1.01      inference(unflattening,[status(thm)],[c_582]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4484,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.06/1.01      | r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top
% 3.06/1.01      | v1_relat_1(sK5) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_584,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.06/1.01      | r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top
% 3.06/1.01      | v1_relat_1(sK5) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5193,plain,
% 3.06/1.01      ( r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top
% 3.06/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_4484,c_35,c_584,c_4746]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5194,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.06/1.01      | r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top ),
% 3.06/1.01      inference(renaming,[status(thm)],[c_5193]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5713,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.06/1.01      | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),X0) != iProver_top ),
% 3.06/1.01      inference(demodulation,[status(thm)],[c_5707,c_5194]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_7952,plain,
% 3.06/1.01      ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5)
% 3.06/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_7940,c_5713]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8100,plain,
% 3.06/1.01      ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5) ),
% 3.06/1.01      inference(forward_subsumption_resolution,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_7952,c_4494]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.01      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.06/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4496,plain,
% 3.06/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.06/1.01      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8101,plain,
% 3.06/1.01      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top
% 3.06/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_8100,c_4496]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5359,plain,
% 3.06/1.01      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_4492,c_4494]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.06/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_239,plain,
% 3.06/1.01      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.06/1.01      inference(prop_impl,[status(thm)],[c_5]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_240,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.06/1.01      inference(renaming,[status(thm)],[c_239]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_24,negated_conjecture,
% 3.06/1.01      ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) ),
% 3.06/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_432,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.06/1.01      | k2_relset_1(sK3,sK4,sK5) != X0
% 3.06/1.01      | sK2 != X1 ),
% 3.06/1.01      inference(resolution_lifted,[status(thm)],[c_240,c_24]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_433,plain,
% 3.06/1.01      ( ~ m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK2)) ),
% 3.06/1.01      inference(unflattening,[status(thm)],[c_432]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4486,plain,
% 3.06/1.01      ( m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK2)) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5480,plain,
% 3.06/1.01      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK2)) != iProver_top ),
% 3.06/1.01      inference(demodulation,[status(thm)],[c_5359,c_4486]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8903,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_8101,c_5480]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8908,plain,
% 3.06/1.01      ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK2,sK5)) = k1_funct_1(sK5,sK1(sK3,sK2,sK5)) ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_6787,c_8903]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8974,plain,
% 3.06/1.01      ( m1_subset_1(sK1(sK3,sK2,sK5),sK3) != iProver_top
% 3.06/1.01      | r2_hidden(k1_funct_1(sK5,sK1(sK3,sK2,sK5)),sK2) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_8908,c_4493]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8909,plain,
% 3.06/1.01      ( r2_hidden(sK1(sK3,sK2,sK5),sK3) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_5712,c_8903]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8918,plain,
% 3.06/1.01      ( m1_subset_1(sK1(sK3,sK2,sK5),sK3) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_8909,c_4498]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8986,plain,
% 3.06/1.01      ( r2_hidden(k1_funct_1(sK5,sK1(sK3,sK2,sK5)),sK2) = iProver_top ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_8974,c_8918]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8995,plain,
% 3.06/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_8986,c_5713]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(contradiction,plain,
% 3.06/1.01      ( $false ),
% 3.06/1.01      inference(minisat,[status(thm)],[c_8995,c_8101,c_5480]) ).
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/1.01  
% 3.06/1.01  ------                               Statistics
% 3.06/1.01  
% 3.06/1.01  ------ General
% 3.06/1.01  
% 3.06/1.01  abstr_ref_over_cycles:                  0
% 3.06/1.01  abstr_ref_under_cycles:                 0
% 3.06/1.01  gc_basic_clause_elim:                   0
% 3.06/1.01  forced_gc_time:                         0
% 3.06/1.01  parsing_time:                           0.011
% 3.06/1.01  unif_index_cands_time:                  0.
% 3.06/1.01  unif_index_add_time:                    0.
% 3.06/1.01  orderings_time:                         0.
% 3.06/1.01  out_proof_time:                         0.009
% 3.06/1.01  total_time:                             0.241
% 3.06/1.01  num_of_symbols:                         55
% 3.06/1.01  num_of_terms:                           4886
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing
% 3.06/1.01  
% 3.06/1.01  num_of_splits:                          2
% 3.06/1.01  num_of_split_atoms:                     2
% 3.06/1.01  num_of_reused_defs:                     0
% 3.06/1.01  num_eq_ax_congr_red:                    13
% 3.06/1.01  num_of_sem_filtered_clauses:            1
% 3.06/1.01  num_of_subtypes:                        0
% 3.06/1.01  monotx_restored_types:                  0
% 3.06/1.01  sat_num_of_epr_types:                   0
% 3.06/1.01  sat_num_of_non_cyclic_types:            0
% 3.06/1.01  sat_guarded_non_collapsed_types:        0
% 3.06/1.01  num_pure_diseq_elim:                    0
% 3.06/1.01  simp_replaced_by:                       0
% 3.06/1.01  res_preprocessed:                       124
% 3.06/1.01  prep_upred:                             0
% 3.06/1.01  prep_unflattend:                        272
% 3.06/1.01  smt_new_axioms:                         0
% 3.06/1.01  pred_elim_cands:                        7
% 3.06/1.01  pred_elim:                              3
% 3.06/1.01  pred_elim_cl:                           -2
% 3.06/1.01  pred_elim_cycles:                       11
% 3.06/1.01  merged_defs:                            2
% 3.06/1.01  merged_defs_ncl:                        0
% 3.06/1.01  bin_hyper_res:                          2
% 3.06/1.01  prep_cycles:                            3
% 3.06/1.01  pred_elim_time:                         0.08
% 3.06/1.01  splitting_time:                         0.
% 3.06/1.01  sem_filter_time:                        0.
% 3.06/1.01  monotx_time:                            0.
% 3.06/1.01  subtype_inf_time:                       0.
% 3.06/1.01  
% 3.06/1.01  ------ Problem properties
% 3.06/1.01  
% 3.06/1.01  clauses:                                33
% 3.06/1.01  conjectures:                            4
% 3.06/1.01  epr:                                    8
% 3.06/1.01  horn:                                   22
% 3.06/1.01  ground:                                 12
% 3.06/1.01  unary:                                  10
% 3.06/1.01  binary:                                 11
% 3.06/1.01  lits:                                   79
% 3.06/1.01  lits_eq:                                24
% 3.06/1.01  fd_pure:                                0
% 3.06/1.01  fd_pseudo:                              0
% 3.06/1.01  fd_cond:                                4
% 3.06/1.01  fd_pseudo_cond:                         0
% 3.06/1.01  ac_symbols:                             0
% 3.06/1.01  
% 3.06/1.01  ------ Propositional Solver
% 3.06/1.01  
% 3.06/1.01  prop_solver_calls:                      23
% 3.06/1.01  prop_fast_solver_calls:                 1691
% 3.06/1.01  smt_solver_calls:                       0
% 3.06/1.01  smt_fast_solver_calls:                  0
% 3.06/1.01  prop_num_of_clauses:                    2388
% 3.06/1.01  prop_preprocess_simplified:             6931
% 3.06/1.01  prop_fo_subsumed:                       65
% 3.06/1.01  prop_solver_time:                       0.
% 3.06/1.01  smt_solver_time:                        0.
% 3.06/1.01  smt_fast_solver_time:                   0.
% 3.06/1.01  prop_fast_solver_time:                  0.
% 3.06/1.01  prop_unsat_core_time:                   0.
% 3.06/1.01  
% 3.06/1.01  ------ QBF
% 3.06/1.01  
% 3.06/1.01  qbf_q_res:                              0
% 3.06/1.01  qbf_num_tautologies:                    0
% 3.06/1.01  qbf_prep_cycles:                        0
% 3.06/1.01  
% 3.06/1.01  ------ BMC1
% 3.06/1.01  
% 3.06/1.01  bmc1_current_bound:                     -1
% 3.06/1.01  bmc1_last_solved_bound:                 -1
% 3.06/1.01  bmc1_unsat_core_size:                   -1
% 3.06/1.01  bmc1_unsat_core_parents_size:           -1
% 3.06/1.01  bmc1_merge_next_fun:                    0
% 3.06/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.06/1.01  
% 3.06/1.01  ------ Instantiation
% 3.06/1.01  
% 3.06/1.01  inst_num_of_clauses:                    686
% 3.06/1.01  inst_num_in_passive:                    12
% 3.06/1.01  inst_num_in_active:                     396
% 3.06/1.01  inst_num_in_unprocessed:                278
% 3.06/1.01  inst_num_of_loops:                      430
% 3.06/1.01  inst_num_of_learning_restarts:          0
% 3.06/1.01  inst_num_moves_active_passive:          32
% 3.06/1.01  inst_lit_activity:                      0
% 3.06/1.01  inst_lit_activity_moves:                0
% 3.06/1.01  inst_num_tautologies:                   0
% 3.06/1.01  inst_num_prop_implied:                  0
% 3.06/1.01  inst_num_existing_simplified:           0
% 3.06/1.01  inst_num_eq_res_simplified:             0
% 3.06/1.01  inst_num_child_elim:                    0
% 3.06/1.01  inst_num_of_dismatching_blockings:      244
% 3.06/1.01  inst_num_of_non_proper_insts:           634
% 3.06/1.01  inst_num_of_duplicates:                 0
% 3.06/1.01  inst_inst_num_from_inst_to_res:         0
% 3.06/1.01  inst_dismatching_checking_time:         0.
% 3.06/1.01  
% 3.06/1.01  ------ Resolution
% 3.06/1.01  
% 3.06/1.01  res_num_of_clauses:                     0
% 3.06/1.01  res_num_in_passive:                     0
% 3.06/1.01  res_num_in_active:                      0
% 3.06/1.01  res_num_of_loops:                       127
% 3.06/1.01  res_forward_subset_subsumed:            44
% 3.06/1.01  res_backward_subset_subsumed:           0
% 3.06/1.01  res_forward_subsumed:                   8
% 3.06/1.01  res_backward_subsumed:                  9
% 3.06/1.01  res_forward_subsumption_resolution:     10
% 3.06/1.01  res_backward_subsumption_resolution:    1
% 3.06/1.01  res_clause_to_clause_subsumption:       462
% 3.06/1.01  res_orphan_elimination:                 0
% 3.06/1.01  res_tautology_del:                      80
% 3.06/1.01  res_num_eq_res_simplified:              0
% 3.06/1.01  res_num_sel_changes:                    0
% 3.06/1.01  res_moves_from_active_to_pass:          0
% 3.06/1.01  
% 3.06/1.01  ------ Superposition
% 3.06/1.01  
% 3.06/1.01  sup_time_total:                         0.
% 3.06/1.01  sup_time_generating:                    0.
% 3.06/1.01  sup_time_sim_full:                      0.
% 3.06/1.01  sup_time_sim_immed:                     0.
% 3.06/1.01  
% 3.06/1.01  sup_num_of_clauses:                     102
% 3.06/1.01  sup_num_in_active:                      77
% 3.06/1.01  sup_num_in_passive:                     25
% 3.06/1.01  sup_num_of_loops:                       85
% 3.06/1.01  sup_fw_superposition:                   23
% 3.06/1.01  sup_bw_superposition:                   90
% 3.06/1.01  sup_immediate_simplified:               26
% 3.06/1.01  sup_given_eliminated:                   0
% 3.06/1.01  comparisons_done:                       0
% 3.06/1.01  comparisons_avoided:                    9
% 3.06/1.01  
% 3.06/1.01  ------ Simplifications
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  sim_fw_subset_subsumed:                 17
% 3.06/1.01  sim_bw_subset_subsumed:                 6
% 3.06/1.01  sim_fw_subsumed:                        3
% 3.06/1.01  sim_bw_subsumed:                        0
% 3.06/1.01  sim_fw_subsumption_res:                 3
% 3.06/1.01  sim_bw_subsumption_res:                 0
% 3.06/1.01  sim_tautology_del:                      1
% 3.06/1.01  sim_eq_tautology_del:                   0
% 3.06/1.01  sim_eq_res_simp:                        0
% 3.06/1.01  sim_fw_demodulated:                     2
% 3.06/1.01  sim_bw_demodulated:                     8
% 3.06/1.01  sim_light_normalised:                   12
% 3.06/1.01  sim_joinable_taut:                      0
% 3.06/1.01  sim_joinable_simp:                      0
% 3.06/1.01  sim_ac_normalised:                      0
% 3.06/1.01  sim_smt_subsumption:                    0
% 3.06/1.01  
%------------------------------------------------------------------------------
