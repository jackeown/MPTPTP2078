%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:15 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  158 (2308 expanded)
%              Number of clauses        :   92 ( 720 expanded)
%              Number of leaves         :   19 ( 626 expanded)
%              Depth                    :   26
%              Number of atoms          :  508 (13358 expanded)
%              Number of equality atoms :  158 (1277 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1)
        & r2_hidden(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1)
        & r2_hidden(sK1(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f38])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK1(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK1(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f68])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f43,plain,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2)
        | ~ m1_subset_1(X4,sK3) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f42,f41,f40])).

fof(f72,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f37,plain,(
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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f34])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2)
      | ~ m1_subset_1(X4,sK3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK1(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f69])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | r2_hidden(sK1(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1050,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | r2_hidden(sK1(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_1051,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
    | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_1050])).

cnf(c_2379,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1051])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1052,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1051])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2706,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2707,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2706])).

cnf(c_3185,plain,
    ( r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2379,c_37,c_1052,c_2707])).

cnf(c_3186,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3185])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2392,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3193,plain,
    ( m1_subset_1(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3186,c_2392])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1317,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_1318,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_1317])).

cnf(c_1320,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1318,c_28])).

cnf(c_2386,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2389,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3282,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2386,c_2389])).

cnf(c_3516,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1320,c_3282])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_531,plain,
    ( ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | X1 != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_532,plain,
    ( ~ r1_xboole_0(k1_xboole_0,X0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_628,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | v1_xboole_0(k1_xboole_0)
    | X2 != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_532])).

cnf(c_629,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0),k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_513,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_514,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_637,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_629,c_514])).

cnf(c_784,plain,
    ( sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_637])).

cnf(c_3613,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3516,c_784])).

cnf(c_4658,plain,
    ( m1_subset_1(sK1(sK3,X0,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3193,c_3613])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_739,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_32])).

cnf(c_740,plain,
    ( ~ v1_funct_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ m1_subset_1(X2,sK3)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK3,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_984,plain,
    ( ~ v1_funct_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ m1_subset_1(X2,sK3)
    | k3_funct_2(sK3,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_740,c_30])).

cnf(c_985,plain,
    ( ~ v1_funct_2(sK5,sK3,X0)
    | ~ m1_subset_1(X1,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
    | k3_funct_2(sK3,X0,sK5,X1) = k1_funct_1(sK5,X1) ),
    inference(unflattening,[status(thm)],[c_984])).

cnf(c_1418,plain,
    ( ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | k3_funct_2(sK3,X1,sK5,X0) = k1_funct_1(sK5,X0)
    | sK5 != sK5
    | sK4 != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_985])).

cnf(c_1419,plain,
    ( ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_1418])).

cnf(c_1423,plain,
    ( ~ m1_subset_1(X0,sK3)
    | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1419,c_28])).

cnf(c_2366,plain,
    ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1423])).

cnf(c_4666,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,X0,sK5)) = k1_funct_1(sK5,sK1(sK3,X0,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4658,c_2366])).

cnf(c_3618,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3613,c_3186])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2388,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4931,plain,
    ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
    | r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3618,c_2388])).

cnf(c_5204,plain,
    ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
    | m1_subset_1(sK1(sK3,X0,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4931,c_2392])).

cnf(c_5236,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,X0,sK5)) = k1_funct_1(sK5,sK1(sK3,X0,sK5))
    | k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_5204,c_2366])).

cnf(c_27,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2387,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5527,plain,
    ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
    | m1_subset_1(sK1(sK3,X0,sK5),sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5236,c_2387])).

cnf(c_5903,plain,
    ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
    | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5527,c_5204])).

cnf(c_20,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r2_hidden(k1_funct_1(X0,sK1(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1065,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r2_hidden(k1_funct_1(X0,sK1(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_1066,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
    | ~ r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_1065])).

cnf(c_2378,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1066])).

cnf(c_1067,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1066])).

cnf(c_3123,plain,
    ( r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2378,c_37,c_1067,c_2707])).

cnf(c_3124,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3123])).

cnf(c_3619,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3613,c_3124])).

cnf(c_5915,plain,
    ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5903,c_3619])).

cnf(c_6044,plain,
    ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5915,c_2388])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2390,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6045,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6044,c_2390])).

cnf(c_3278,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2386,c_2388])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_253,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_254,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_253])).

cnf(c_26,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k2_relset_1(sK3,sK4,sK5) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_254,c_26])).

cnf(c_549,plain,
    ( ~ m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_2382,plain,
    ( m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_549])).

cnf(c_3479,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3278,c_2382])).

cnf(c_6322,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6045,c_3479])).

cnf(c_6423,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK2,sK5)) = k1_funct_1(sK5,sK1(sK3,sK2,sK5)) ),
    inference(superposition,[status(thm)],[c_4666,c_6322])).

cnf(c_7987,plain,
    ( m1_subset_1(sK1(sK3,sK2,sK5),sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(sK3,sK2,sK5)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6423,c_2387])).

cnf(c_6327,plain,
    ( r2_hidden(sK1(sK3,sK2,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3618,c_6322])).

cnf(c_7554,plain,
    ( m1_subset_1(sK1(sK3,sK2,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6327,c_2392])).

cnf(c_8008,plain,
    ( r2_hidden(k1_funct_1(sK5,sK1(sK3,sK2,sK5)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7987,c_7554])).

cnf(c_8017,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8008,c_3619])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8017,c_6045,c_3479])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.07  % Command    : iproveropt_run.sh %d %s
% 0.06/0.25  % Computer   : n016.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 16:02:19 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  % Running in FOF mode
% 3.25/0.87  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/0.87  
% 3.25/0.87  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.25/0.87  
% 3.25/0.87  ------  iProver source info
% 3.25/0.87  
% 3.25/0.87  git: date: 2020-06-30 10:37:57 +0100
% 3.25/0.87  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.25/0.87  git: non_committed_changes: false
% 3.25/0.87  git: last_make_outside_of_git: false
% 3.25/0.87  
% 3.25/0.87  ------ 
% 3.25/0.87  
% 3.25/0.87  ------ Input Options
% 3.25/0.87  
% 3.25/0.87  --out_options                           all
% 3.25/0.87  --tptp_safe_out                         true
% 3.25/0.87  --problem_path                          ""
% 3.25/0.87  --include_path                          ""
% 3.25/0.87  --clausifier                            res/vclausify_rel
% 3.25/0.87  --clausifier_options                    --mode clausify
% 3.25/0.87  --stdin                                 false
% 3.25/0.87  --stats_out                             all
% 3.25/0.87  
% 3.25/0.87  ------ General Options
% 3.25/0.87  
% 3.25/0.87  --fof                                   false
% 3.25/0.87  --time_out_real                         305.
% 3.25/0.87  --time_out_virtual                      -1.
% 3.25/0.87  --symbol_type_check                     false
% 3.25/0.87  --clausify_out                          false
% 3.25/0.87  --sig_cnt_out                           false
% 3.25/0.87  --trig_cnt_out                          false
% 3.25/0.87  --trig_cnt_out_tolerance                1.
% 3.25/0.87  --trig_cnt_out_sk_spl                   false
% 3.25/0.87  --abstr_cl_out                          false
% 3.25/0.87  
% 3.25/0.87  ------ Global Options
% 3.25/0.87  
% 3.25/0.87  --schedule                              default
% 3.25/0.87  --add_important_lit                     false
% 3.25/0.87  --prop_solver_per_cl                    1000
% 3.25/0.87  --min_unsat_core                        false
% 3.25/0.87  --soft_assumptions                      false
% 3.25/0.87  --soft_lemma_size                       3
% 3.25/0.87  --prop_impl_unit_size                   0
% 3.25/0.87  --prop_impl_unit                        []
% 3.25/0.87  --share_sel_clauses                     true
% 3.25/0.87  --reset_solvers                         false
% 3.25/0.87  --bc_imp_inh                            [conj_cone]
% 3.25/0.87  --conj_cone_tolerance                   3.
% 3.25/0.87  --extra_neg_conj                        none
% 3.25/0.87  --large_theory_mode                     true
% 3.25/0.87  --prolific_symb_bound                   200
% 3.25/0.87  --lt_threshold                          2000
% 3.25/0.87  --clause_weak_htbl                      true
% 3.25/0.87  --gc_record_bc_elim                     false
% 3.25/0.87  
% 3.25/0.87  ------ Preprocessing Options
% 3.25/0.87  
% 3.25/0.87  --preprocessing_flag                    true
% 3.25/0.87  --time_out_prep_mult                    0.1
% 3.25/0.87  --splitting_mode                        input
% 3.25/0.87  --splitting_grd                         true
% 3.25/0.87  --splitting_cvd                         false
% 3.25/0.87  --splitting_cvd_svl                     false
% 3.25/0.87  --splitting_nvd                         32
% 3.25/0.87  --sub_typing                            true
% 3.25/0.87  --prep_gs_sim                           true
% 3.25/0.87  --prep_unflatten                        true
% 3.25/0.87  --prep_res_sim                          true
% 3.25/0.87  --prep_upred                            true
% 3.25/0.87  --prep_sem_filter                       exhaustive
% 3.25/0.87  --prep_sem_filter_out                   false
% 3.25/0.87  --pred_elim                             true
% 3.25/0.87  --res_sim_input                         true
% 3.25/0.87  --eq_ax_congr_red                       true
% 3.25/0.87  --pure_diseq_elim                       true
% 3.25/0.87  --brand_transform                       false
% 3.25/0.87  --non_eq_to_eq                          false
% 3.25/0.87  --prep_def_merge                        true
% 3.25/0.87  --prep_def_merge_prop_impl              false
% 3.25/0.87  --prep_def_merge_mbd                    true
% 3.25/0.87  --prep_def_merge_tr_red                 false
% 3.25/0.87  --prep_def_merge_tr_cl                  false
% 3.25/0.87  --smt_preprocessing                     true
% 3.25/0.87  --smt_ac_axioms                         fast
% 3.25/0.87  --preprocessed_out                      false
% 3.25/0.87  --preprocessed_stats                    false
% 3.25/0.87  
% 3.25/0.87  ------ Abstraction refinement Options
% 3.25/0.87  
% 3.25/0.87  --abstr_ref                             []
% 3.25/0.87  --abstr_ref_prep                        false
% 3.25/0.87  --abstr_ref_until_sat                   false
% 3.25/0.87  --abstr_ref_sig_restrict                funpre
% 3.25/0.87  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/0.87  --abstr_ref_under                       []
% 3.25/0.87  
% 3.25/0.87  ------ SAT Options
% 3.25/0.87  
% 3.25/0.87  --sat_mode                              false
% 3.25/0.87  --sat_fm_restart_options                ""
% 3.25/0.87  --sat_gr_def                            false
% 3.25/0.87  --sat_epr_types                         true
% 3.25/0.87  --sat_non_cyclic_types                  false
% 3.25/0.87  --sat_finite_models                     false
% 3.25/0.87  --sat_fm_lemmas                         false
% 3.25/0.87  --sat_fm_prep                           false
% 3.25/0.87  --sat_fm_uc_incr                        true
% 3.25/0.87  --sat_out_model                         small
% 3.25/0.87  --sat_out_clauses                       false
% 3.25/0.87  
% 3.25/0.87  ------ QBF Options
% 3.25/0.87  
% 3.25/0.87  --qbf_mode                              false
% 3.25/0.87  --qbf_elim_univ                         false
% 3.25/0.87  --qbf_dom_inst                          none
% 3.25/0.87  --qbf_dom_pre_inst                      false
% 3.25/0.87  --qbf_sk_in                             false
% 3.25/0.87  --qbf_pred_elim                         true
% 3.25/0.87  --qbf_split                             512
% 3.25/0.87  
% 3.25/0.87  ------ BMC1 Options
% 3.25/0.87  
% 3.25/0.87  --bmc1_incremental                      false
% 3.25/0.87  --bmc1_axioms                           reachable_all
% 3.25/0.87  --bmc1_min_bound                        0
% 3.25/0.87  --bmc1_max_bound                        -1
% 3.25/0.87  --bmc1_max_bound_default                -1
% 3.25/0.87  --bmc1_symbol_reachability              true
% 3.25/0.87  --bmc1_property_lemmas                  false
% 3.25/0.87  --bmc1_k_induction                      false
% 3.25/0.87  --bmc1_non_equiv_states                 false
% 3.25/0.87  --bmc1_deadlock                         false
% 3.25/0.87  --bmc1_ucm                              false
% 3.25/0.87  --bmc1_add_unsat_core                   none
% 3.25/0.87  --bmc1_unsat_core_children              false
% 3.25/0.87  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/0.87  --bmc1_out_stat                         full
% 3.25/0.87  --bmc1_ground_init                      false
% 3.25/0.87  --bmc1_pre_inst_next_state              false
% 3.25/0.87  --bmc1_pre_inst_state                   false
% 3.25/0.87  --bmc1_pre_inst_reach_state             false
% 3.25/0.87  --bmc1_out_unsat_core                   false
% 3.25/0.87  --bmc1_aig_witness_out                  false
% 3.25/0.87  --bmc1_verbose                          false
% 3.25/0.87  --bmc1_dump_clauses_tptp                false
% 3.25/0.87  --bmc1_dump_unsat_core_tptp             false
% 3.25/0.87  --bmc1_dump_file                        -
% 3.25/0.87  --bmc1_ucm_expand_uc_limit              128
% 3.25/0.87  --bmc1_ucm_n_expand_iterations          6
% 3.25/0.87  --bmc1_ucm_extend_mode                  1
% 3.25/0.87  --bmc1_ucm_init_mode                    2
% 3.25/0.87  --bmc1_ucm_cone_mode                    none
% 3.25/0.87  --bmc1_ucm_reduced_relation_type        0
% 3.25/0.87  --bmc1_ucm_relax_model                  4
% 3.25/0.87  --bmc1_ucm_full_tr_after_sat            true
% 3.25/0.87  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/0.87  --bmc1_ucm_layered_model                none
% 3.25/0.87  --bmc1_ucm_max_lemma_size               10
% 3.25/0.87  
% 3.25/0.87  ------ AIG Options
% 3.25/0.87  
% 3.25/0.87  --aig_mode                              false
% 3.25/0.87  
% 3.25/0.87  ------ Instantiation Options
% 3.25/0.87  
% 3.25/0.87  --instantiation_flag                    true
% 3.25/0.87  --inst_sos_flag                         false
% 3.25/0.87  --inst_sos_phase                        true
% 3.25/0.87  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/0.87  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/0.87  --inst_lit_sel_side                     num_symb
% 3.25/0.87  --inst_solver_per_active                1400
% 3.25/0.87  --inst_solver_calls_frac                1.
% 3.25/0.87  --inst_passive_queue_type               priority_queues
% 3.25/0.87  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/0.87  --inst_passive_queues_freq              [25;2]
% 3.25/0.87  --inst_dismatching                      true
% 3.25/0.87  --inst_eager_unprocessed_to_passive     true
% 3.25/0.87  --inst_prop_sim_given                   true
% 3.25/0.87  --inst_prop_sim_new                     false
% 3.25/0.87  --inst_subs_new                         false
% 3.25/0.87  --inst_eq_res_simp                      false
% 3.25/0.87  --inst_subs_given                       false
% 3.25/0.87  --inst_orphan_elimination               true
% 3.25/0.87  --inst_learning_loop_flag               true
% 3.25/0.87  --inst_learning_start                   3000
% 3.25/0.87  --inst_learning_factor                  2
% 3.25/0.87  --inst_start_prop_sim_after_learn       3
% 3.25/0.87  --inst_sel_renew                        solver
% 3.25/0.87  --inst_lit_activity_flag                true
% 3.25/0.87  --inst_restr_to_given                   false
% 3.25/0.87  --inst_activity_threshold               500
% 3.25/0.87  --inst_out_proof                        true
% 3.25/0.87  
% 3.25/0.87  ------ Resolution Options
% 3.25/0.87  
% 3.25/0.87  --resolution_flag                       true
% 3.25/0.87  --res_lit_sel                           adaptive
% 3.25/0.87  --res_lit_sel_side                      none
% 3.25/0.87  --res_ordering                          kbo
% 3.25/0.87  --res_to_prop_solver                    active
% 3.25/0.87  --res_prop_simpl_new                    false
% 3.25/0.87  --res_prop_simpl_given                  true
% 3.25/0.87  --res_passive_queue_type                priority_queues
% 3.25/0.87  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/0.87  --res_passive_queues_freq               [15;5]
% 3.25/0.87  --res_forward_subs                      full
% 3.25/0.87  --res_backward_subs                     full
% 3.25/0.87  --res_forward_subs_resolution           true
% 3.25/0.87  --res_backward_subs_resolution          true
% 3.25/0.87  --res_orphan_elimination                true
% 3.25/0.87  --res_time_limit                        2.
% 3.25/0.87  --res_out_proof                         true
% 3.25/0.87  
% 3.25/0.87  ------ Superposition Options
% 3.25/0.87  
% 3.25/0.87  --superposition_flag                    true
% 3.25/0.87  --sup_passive_queue_type                priority_queues
% 3.25/0.87  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/0.87  --sup_passive_queues_freq               [8;1;4]
% 3.25/0.87  --demod_completeness_check              fast
% 3.25/0.87  --demod_use_ground                      true
% 3.25/0.87  --sup_to_prop_solver                    passive
% 3.25/0.87  --sup_prop_simpl_new                    true
% 3.25/0.87  --sup_prop_simpl_given                  true
% 3.25/0.87  --sup_fun_splitting                     false
% 3.25/0.87  --sup_smt_interval                      50000
% 3.25/0.87  
% 3.25/0.87  ------ Superposition Simplification Setup
% 3.25/0.87  
% 3.25/0.87  --sup_indices_passive                   []
% 3.25/0.87  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.87  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.87  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.87  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/0.87  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.87  --sup_full_bw                           [BwDemod]
% 3.25/0.87  --sup_immed_triv                        [TrivRules]
% 3.25/0.87  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/0.87  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.87  --sup_immed_bw_main                     []
% 3.25/0.87  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.87  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/0.87  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.87  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.87  
% 3.25/0.87  ------ Combination Options
% 3.25/0.87  
% 3.25/0.87  --comb_res_mult                         3
% 3.25/0.87  --comb_sup_mult                         2
% 3.25/0.87  --comb_inst_mult                        10
% 3.25/0.87  
% 3.25/0.87  ------ Debug Options
% 3.25/0.87  
% 3.25/0.87  --dbg_backtrace                         false
% 3.25/0.87  --dbg_dump_prop_clauses                 false
% 3.25/0.87  --dbg_dump_prop_clauses_file            -
% 3.25/0.87  --dbg_out_stat                          false
% 3.25/0.87  ------ Parsing...
% 3.25/0.87  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.25/0.87  
% 3.25/0.87  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 3.25/0.87  
% 3.25/0.87  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.25/0.87  
% 3.25/0.87  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.25/0.87  ------ Proving...
% 3.25/0.87  ------ Problem Properties 
% 3.25/0.87  
% 3.25/0.87  
% 3.25/0.87  clauses                                 40
% 3.25/0.87  conjectures                             2
% 3.25/0.87  EPR                                     5
% 3.25/0.87  Horn                                    26
% 3.25/0.87  unary                                   7
% 3.25/0.87  binary                                  13
% 3.25/0.87  lits                                    112
% 3.25/0.87  lits eq                                 40
% 3.25/0.87  fd_pure                                 0
% 3.25/0.87  fd_pseudo                               0
% 3.25/0.87  fd_cond                                 4
% 3.25/0.87  fd_pseudo_cond                          0
% 3.25/0.87  AC symbols                              0
% 3.25/0.87  
% 3.25/0.87  ------ Schedule dynamic 5 is on 
% 3.25/0.87  
% 3.25/0.87  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.25/0.87  
% 3.25/0.87  
% 3.25/0.87  ------ 
% 3.25/0.87  Current options:
% 3.25/0.87  ------ 
% 3.25/0.87  
% 3.25/0.87  ------ Input Options
% 3.25/0.87  
% 3.25/0.87  --out_options                           all
% 3.25/0.87  --tptp_safe_out                         true
% 3.25/0.87  --problem_path                          ""
% 3.25/0.87  --include_path                          ""
% 3.25/0.87  --clausifier                            res/vclausify_rel
% 3.25/0.87  --clausifier_options                    --mode clausify
% 3.25/0.87  --stdin                                 false
% 3.25/0.87  --stats_out                             all
% 3.25/0.87  
% 3.25/0.87  ------ General Options
% 3.25/0.87  
% 3.25/0.87  --fof                                   false
% 3.25/0.87  --time_out_real                         305.
% 3.25/0.87  --time_out_virtual                      -1.
% 3.25/0.87  --symbol_type_check                     false
% 3.25/0.87  --clausify_out                          false
% 3.25/0.87  --sig_cnt_out                           false
% 3.25/0.87  --trig_cnt_out                          false
% 3.25/0.87  --trig_cnt_out_tolerance                1.
% 3.25/0.87  --trig_cnt_out_sk_spl                   false
% 3.25/0.87  --abstr_cl_out                          false
% 3.25/0.87  
% 3.25/0.87  ------ Global Options
% 3.25/0.87  
% 3.25/0.87  --schedule                              default
% 3.25/0.87  --add_important_lit                     false
% 3.25/0.87  --prop_solver_per_cl                    1000
% 3.25/0.87  --min_unsat_core                        false
% 3.25/0.87  --soft_assumptions                      false
% 3.25/0.87  --soft_lemma_size                       3
% 3.25/0.87  --prop_impl_unit_size                   0
% 3.25/0.87  --prop_impl_unit                        []
% 3.25/0.87  --share_sel_clauses                     true
% 3.25/0.87  --reset_solvers                         false
% 3.25/0.87  --bc_imp_inh                            [conj_cone]
% 3.25/0.87  --conj_cone_tolerance                   3.
% 3.25/0.87  --extra_neg_conj                        none
% 3.25/0.87  --large_theory_mode                     true
% 3.25/0.87  --prolific_symb_bound                   200
% 3.25/0.87  --lt_threshold                          2000
% 3.25/0.87  --clause_weak_htbl                      true
% 3.25/0.87  --gc_record_bc_elim                     false
% 3.25/0.87  
% 3.25/0.87  ------ Preprocessing Options
% 3.25/0.87  
% 3.25/0.87  --preprocessing_flag                    true
% 3.25/0.87  --time_out_prep_mult                    0.1
% 3.25/0.87  --splitting_mode                        input
% 3.25/0.87  --splitting_grd                         true
% 3.25/0.87  --splitting_cvd                         false
% 3.25/0.87  --splitting_cvd_svl                     false
% 3.25/0.87  --splitting_nvd                         32
% 3.25/0.87  --sub_typing                            true
% 3.25/0.87  --prep_gs_sim                           true
% 3.25/0.87  --prep_unflatten                        true
% 3.25/0.87  --prep_res_sim                          true
% 3.25/0.87  --prep_upred                            true
% 3.25/0.87  --prep_sem_filter                       exhaustive
% 3.25/0.87  --prep_sem_filter_out                   false
% 3.25/0.87  --pred_elim                             true
% 3.25/0.87  --res_sim_input                         true
% 3.25/0.87  --eq_ax_congr_red                       true
% 3.25/0.87  --pure_diseq_elim                       true
% 3.25/0.87  --brand_transform                       false
% 3.25/0.87  --non_eq_to_eq                          false
% 3.25/0.87  --prep_def_merge                        true
% 3.25/0.87  --prep_def_merge_prop_impl              false
% 3.25/0.87  --prep_def_merge_mbd                    true
% 3.25/0.87  --prep_def_merge_tr_red                 false
% 3.25/0.87  --prep_def_merge_tr_cl                  false
% 3.25/0.87  --smt_preprocessing                     true
% 3.25/0.87  --smt_ac_axioms                         fast
% 3.25/0.87  --preprocessed_out                      false
% 3.25/0.87  --preprocessed_stats                    false
% 3.25/0.87  
% 3.25/0.87  ------ Abstraction refinement Options
% 3.25/0.87  
% 3.25/0.87  --abstr_ref                             []
% 3.25/0.87  --abstr_ref_prep                        false
% 3.25/0.87  --abstr_ref_until_sat                   false
% 3.25/0.87  --abstr_ref_sig_restrict                funpre
% 3.25/0.87  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/0.87  --abstr_ref_under                       []
% 3.25/0.87  
% 3.25/0.87  ------ SAT Options
% 3.25/0.87  
% 3.25/0.87  --sat_mode                              false
% 3.25/0.87  --sat_fm_restart_options                ""
% 3.25/0.87  --sat_gr_def                            false
% 3.25/0.87  --sat_epr_types                         true
% 3.25/0.87  --sat_non_cyclic_types                  false
% 3.25/0.87  --sat_finite_models                     false
% 3.25/0.87  --sat_fm_lemmas                         false
% 3.25/0.87  --sat_fm_prep                           false
% 3.25/0.87  --sat_fm_uc_incr                        true
% 3.25/0.87  --sat_out_model                         small
% 3.25/0.87  --sat_out_clauses                       false
% 3.25/0.87  
% 3.25/0.87  ------ QBF Options
% 3.25/0.87  
% 3.25/0.87  --qbf_mode                              false
% 3.25/0.87  --qbf_elim_univ                         false
% 3.25/0.87  --qbf_dom_inst                          none
% 3.25/0.87  --qbf_dom_pre_inst                      false
% 3.25/0.87  --qbf_sk_in                             false
% 3.25/0.87  --qbf_pred_elim                         true
% 3.25/0.87  --qbf_split                             512
% 3.25/0.87  
% 3.25/0.87  ------ BMC1 Options
% 3.25/0.87  
% 3.25/0.87  --bmc1_incremental                      false
% 3.25/0.87  --bmc1_axioms                           reachable_all
% 3.25/0.87  --bmc1_min_bound                        0
% 3.25/0.87  --bmc1_max_bound                        -1
% 3.25/0.87  --bmc1_max_bound_default                -1
% 3.25/0.87  --bmc1_symbol_reachability              true
% 3.25/0.87  --bmc1_property_lemmas                  false
% 3.25/0.87  --bmc1_k_induction                      false
% 3.25/0.87  --bmc1_non_equiv_states                 false
% 3.25/0.87  --bmc1_deadlock                         false
% 3.25/0.87  --bmc1_ucm                              false
% 3.25/0.87  --bmc1_add_unsat_core                   none
% 3.25/0.87  --bmc1_unsat_core_children              false
% 3.25/0.87  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/0.87  --bmc1_out_stat                         full
% 3.25/0.87  --bmc1_ground_init                      false
% 3.25/0.87  --bmc1_pre_inst_next_state              false
% 3.25/0.87  --bmc1_pre_inst_state                   false
% 3.25/0.87  --bmc1_pre_inst_reach_state             false
% 3.25/0.87  --bmc1_out_unsat_core                   false
% 3.25/0.87  --bmc1_aig_witness_out                  false
% 3.25/0.87  --bmc1_verbose                          false
% 3.25/0.87  --bmc1_dump_clauses_tptp                false
% 3.25/0.87  --bmc1_dump_unsat_core_tptp             false
% 3.25/0.87  --bmc1_dump_file                        -
% 3.25/0.87  --bmc1_ucm_expand_uc_limit              128
% 3.25/0.87  --bmc1_ucm_n_expand_iterations          6
% 3.25/0.87  --bmc1_ucm_extend_mode                  1
% 3.25/0.87  --bmc1_ucm_init_mode                    2
% 3.25/0.87  --bmc1_ucm_cone_mode                    none
% 3.25/0.87  --bmc1_ucm_reduced_relation_type        0
% 3.25/0.87  --bmc1_ucm_relax_model                  4
% 3.25/0.87  --bmc1_ucm_full_tr_after_sat            true
% 3.25/0.87  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/0.87  --bmc1_ucm_layered_model                none
% 3.25/0.87  --bmc1_ucm_max_lemma_size               10
% 3.25/0.87  
% 3.25/0.87  ------ AIG Options
% 3.25/0.87  
% 3.25/0.87  --aig_mode                              false
% 3.25/0.87  
% 3.25/0.87  ------ Instantiation Options
% 3.25/0.87  
% 3.25/0.87  --instantiation_flag                    true
% 3.25/0.87  --inst_sos_flag                         false
% 3.25/0.87  --inst_sos_phase                        true
% 3.25/0.87  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/0.87  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/0.87  --inst_lit_sel_side                     none
% 3.25/0.87  --inst_solver_per_active                1400
% 3.25/0.87  --inst_solver_calls_frac                1.
% 3.25/0.87  --inst_passive_queue_type               priority_queues
% 3.25/0.87  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/0.87  --inst_passive_queues_freq              [25;2]
% 3.25/0.87  --inst_dismatching                      true
% 3.25/0.87  --inst_eager_unprocessed_to_passive     true
% 3.25/0.87  --inst_prop_sim_given                   true
% 3.25/0.87  --inst_prop_sim_new                     false
% 3.25/0.87  --inst_subs_new                         false
% 3.25/0.87  --inst_eq_res_simp                      false
% 3.25/0.87  --inst_subs_given                       false
% 3.25/0.87  --inst_orphan_elimination               true
% 3.25/0.87  --inst_learning_loop_flag               true
% 3.25/0.87  --inst_learning_start                   3000
% 3.25/0.87  --inst_learning_factor                  2
% 3.25/0.87  --inst_start_prop_sim_after_learn       3
% 3.25/0.87  --inst_sel_renew                        solver
% 3.25/0.87  --inst_lit_activity_flag                true
% 3.25/0.87  --inst_restr_to_given                   false
% 3.25/0.87  --inst_activity_threshold               500
% 3.25/0.87  --inst_out_proof                        true
% 3.25/0.87  
% 3.25/0.87  ------ Resolution Options
% 3.25/0.87  
% 3.25/0.87  --resolution_flag                       false
% 3.25/0.87  --res_lit_sel                           adaptive
% 3.25/0.87  --res_lit_sel_side                      none
% 3.25/0.87  --res_ordering                          kbo
% 3.25/0.87  --res_to_prop_solver                    active
% 3.25/0.87  --res_prop_simpl_new                    false
% 3.25/0.87  --res_prop_simpl_given                  true
% 3.25/0.87  --res_passive_queue_type                priority_queues
% 3.25/0.87  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/0.87  --res_passive_queues_freq               [15;5]
% 3.25/0.87  --res_forward_subs                      full
% 3.25/0.87  --res_backward_subs                     full
% 3.25/0.87  --res_forward_subs_resolution           true
% 3.25/0.87  --res_backward_subs_resolution          true
% 3.25/0.87  --res_orphan_elimination                true
% 3.25/0.87  --res_time_limit                        2.
% 3.25/0.87  --res_out_proof                         true
% 3.25/0.87  
% 3.25/0.87  ------ Superposition Options
% 3.25/0.87  
% 3.25/0.87  --superposition_flag                    true
% 3.25/0.87  --sup_passive_queue_type                priority_queues
% 3.25/0.87  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/0.87  --sup_passive_queues_freq               [8;1;4]
% 3.25/0.87  --demod_completeness_check              fast
% 3.25/0.87  --demod_use_ground                      true
% 3.25/0.87  --sup_to_prop_solver                    passive
% 3.25/0.87  --sup_prop_simpl_new                    true
% 3.25/0.87  --sup_prop_simpl_given                  true
% 3.25/0.87  --sup_fun_splitting                     false
% 3.25/0.87  --sup_smt_interval                      50000
% 3.25/0.87  
% 3.25/0.87  ------ Superposition Simplification Setup
% 3.25/0.87  
% 3.25/0.87  --sup_indices_passive                   []
% 3.25/0.87  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.87  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.87  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.87  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/0.87  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.87  --sup_full_bw                           [BwDemod]
% 3.25/0.87  --sup_immed_triv                        [TrivRules]
% 3.25/0.87  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/0.87  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.87  --sup_immed_bw_main                     []
% 3.25/0.87  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.87  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/0.87  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.87  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.87  
% 3.25/0.87  ------ Combination Options
% 3.25/0.87  
% 3.25/0.87  --comb_res_mult                         3
% 3.25/0.87  --comb_sup_mult                         2
% 3.25/0.87  --comb_inst_mult                        10
% 3.25/0.87  
% 3.25/0.87  ------ Debug Options
% 3.25/0.87  
% 3.25/0.87  --dbg_backtrace                         false
% 3.25/0.87  --dbg_dump_prop_clauses                 false
% 3.25/0.87  --dbg_dump_prop_clauses_file            -
% 3.25/0.87  --dbg_out_stat                          false
% 3.25/0.87  
% 3.25/0.87  
% 3.25/0.87  
% 3.25/0.87  
% 3.25/0.87  ------ Proving...
% 3.25/0.87  
% 3.25/0.87  
% 3.25/0.87  % SZS status Theorem for theBenchmark.p
% 3.25/0.87  
% 3.25/0.87  % SZS output start CNFRefutation for theBenchmark.p
% 3.25/0.87  
% 3.25/0.87  fof(f13,axiom,(
% 3.25/0.87    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.25/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.87  
% 3.25/0.87  fof(f30,plain,(
% 3.25/0.87    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.25/0.87    inference(ennf_transformation,[],[f13])).
% 3.25/0.87  
% 3.25/0.87  fof(f31,plain,(
% 3.25/0.87    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.25/0.87    inference(flattening,[],[f30])).
% 3.25/0.87  
% 3.25/0.87  fof(f38,plain,(
% 3.25/0.87    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),X0)))),
% 3.25/0.87    introduced(choice_axiom,[])).
% 3.25/0.87  
% 3.25/0.87  fof(f39,plain,(
% 3.25/0.87    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.25/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f38])).
% 3.25/0.87  
% 3.25/0.87  fof(f68,plain,(
% 3.25/0.87    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK1(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.25/0.87    inference(cnf_transformation,[],[f39])).
% 3.25/0.87  
% 3.25/0.87  fof(f83,plain,(
% 3.25/0.87    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK1(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.25/0.87    inference(equality_resolution,[],[f68])).
% 3.25/0.87  
% 3.25/0.87  fof(f14,conjecture,(
% 3.25/0.87    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.25/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.87  
% 3.25/0.87  fof(f15,negated_conjecture,(
% 3.25/0.87    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.25/0.87    inference(negated_conjecture,[],[f14])).
% 3.25/0.87  
% 3.25/0.87  fof(f32,plain,(
% 3.25/0.87    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.25/0.87    inference(ennf_transformation,[],[f15])).
% 3.25/0.87  
% 3.25/0.87  fof(f33,plain,(
% 3.25/0.87    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.25/0.87    inference(flattening,[],[f32])).
% 3.25/0.87  
% 3.25/0.87  fof(f42,plain,(
% 3.25/0.87    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK5),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK5,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 3.25/0.87    introduced(choice_axiom,[])).
% 3.25/0.87  
% 3.25/0.87  fof(f41,plain,(
% 3.25/0.87    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK4,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK4,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK4))) & v1_funct_2(X3,X1,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))) )),
% 3.25/0.87    introduced(choice_axiom,[])).
% 3.25/0.87  
% 3.25/0.87  fof(f40,plain,(
% 3.25/0.87    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK3,X2,X3),sK2) & ! [X4] : (r2_hidden(k3_funct_2(sK3,X2,X3,X4),sK2) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X2))) & v1_funct_2(X3,sK3,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))),
% 3.25/0.87    introduced(choice_axiom,[])).
% 3.25/0.87  
% 3.25/0.87  fof(f43,plain,(
% 3.25/0.87    ((~r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) & ! [X4] : (r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)),
% 3.25/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f42,f41,f40])).
% 3.25/0.87  
% 3.25/0.87  fof(f72,plain,(
% 3.25/0.87    v1_funct_1(sK5)),
% 3.25/0.87    inference(cnf_transformation,[],[f43])).
% 3.25/0.87  
% 3.25/0.87  fof(f74,plain,(
% 3.25/0.87    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.25/0.87    inference(cnf_transformation,[],[f43])).
% 3.25/0.87  
% 3.25/0.87  fof(f7,axiom,(
% 3.25/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.25/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.87  
% 3.25/0.87  fof(f22,plain,(
% 3.25/0.87    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.87    inference(ennf_transformation,[],[f7])).
% 3.25/0.87  
% 3.25/0.87  fof(f53,plain,(
% 3.25/0.87    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.87    inference(cnf_transformation,[],[f22])).
% 3.25/0.87  
% 3.25/0.87  fof(f4,axiom,(
% 3.25/0.87    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.25/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.87  
% 3.25/0.87  fof(f20,plain,(
% 3.25/0.87    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.25/0.87    inference(ennf_transformation,[],[f4])).
% 3.25/0.87  
% 3.25/0.87  fof(f49,plain,(
% 3.25/0.87    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.25/0.87    inference(cnf_transformation,[],[f20])).
% 3.25/0.87  
% 3.25/0.87  fof(f11,axiom,(
% 3.25/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.25/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.87  
% 3.25/0.87  fof(f26,plain,(
% 3.25/0.87    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.87    inference(ennf_transformation,[],[f11])).
% 3.25/0.87  
% 3.25/0.87  fof(f27,plain,(
% 3.25/0.87    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.87    inference(flattening,[],[f26])).
% 3.25/0.87  
% 3.25/0.87  fof(f37,plain,(
% 3.25/0.87    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.87    inference(nnf_transformation,[],[f27])).
% 3.25/0.87  
% 3.25/0.87  fof(f57,plain,(
% 3.25/0.87    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.87    inference(cnf_transformation,[],[f37])).
% 3.25/0.87  
% 3.25/0.87  fof(f73,plain,(
% 3.25/0.87    v1_funct_2(sK5,sK3,sK4)),
% 3.25/0.87    inference(cnf_transformation,[],[f43])).
% 3.25/0.87  
% 3.25/0.87  fof(f9,axiom,(
% 3.25/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.25/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.87  
% 3.25/0.87  fof(f24,plain,(
% 3.25/0.87    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.87    inference(ennf_transformation,[],[f9])).
% 3.25/0.87  
% 3.25/0.87  fof(f55,plain,(
% 3.25/0.87    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.87    inference(cnf_transformation,[],[f24])).
% 3.25/0.87  
% 3.25/0.87  fof(f71,plain,(
% 3.25/0.87    ~v1_xboole_0(sK4)),
% 3.25/0.87    inference(cnf_transformation,[],[f43])).
% 3.25/0.87  
% 3.25/0.87  fof(f1,axiom,(
% 3.25/0.87    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.25/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.87  
% 3.25/0.87  fof(f16,plain,(
% 3.25/0.87    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.25/0.87    inference(rectify,[],[f1])).
% 3.25/0.87  
% 3.25/0.87  fof(f17,plain,(
% 3.25/0.87    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.25/0.87    inference(ennf_transformation,[],[f16])).
% 3.25/0.87  
% 3.25/0.87  fof(f34,plain,(
% 3.25/0.87    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.25/0.87    introduced(choice_axiom,[])).
% 3.25/0.87  
% 3.25/0.87  fof(f35,plain,(
% 3.25/0.87    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.25/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f34])).
% 3.25/0.87  
% 3.25/0.87  fof(f44,plain,(
% 3.25/0.87    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.25/0.87    inference(cnf_transformation,[],[f35])).
% 3.25/0.87  
% 3.25/0.87  fof(f2,axiom,(
% 3.25/0.87    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.25/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.87  
% 3.25/0.87  fof(f47,plain,(
% 3.25/0.87    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.25/0.87    inference(cnf_transformation,[],[f2])).
% 3.25/0.87  
% 3.25/0.87  fof(f3,axiom,(
% 3.25/0.87    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.25/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.87  
% 3.25/0.87  fof(f18,plain,(
% 3.25/0.87    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.25/0.87    inference(ennf_transformation,[],[f3])).
% 3.25/0.87  
% 3.25/0.87  fof(f19,plain,(
% 3.25/0.87    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.25/0.87    inference(flattening,[],[f18])).
% 3.25/0.87  
% 3.25/0.87  fof(f48,plain,(
% 3.25/0.87    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.25/0.87    inference(cnf_transformation,[],[f19])).
% 3.25/0.87  
% 3.25/0.87  fof(f6,axiom,(
% 3.25/0.87    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.25/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.87  
% 3.25/0.87  fof(f21,plain,(
% 3.25/0.87    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.25/0.87    inference(ennf_transformation,[],[f6])).
% 3.25/0.87  
% 3.25/0.87  fof(f52,plain,(
% 3.25/0.87    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.25/0.87    inference(cnf_transformation,[],[f21])).
% 3.25/0.87  
% 3.25/0.87  fof(f12,axiom,(
% 3.25/0.87    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.25/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.87  
% 3.25/0.87  fof(f28,plain,(
% 3.25/0.87    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.25/0.87    inference(ennf_transformation,[],[f12])).
% 3.25/0.87  
% 3.25/0.87  fof(f29,plain,(
% 3.25/0.87    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.25/0.87    inference(flattening,[],[f28])).
% 3.25/0.87  
% 3.25/0.87  fof(f63,plain,(
% 3.25/0.87    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.25/0.87    inference(cnf_transformation,[],[f29])).
% 3.25/0.87  
% 3.25/0.87  fof(f70,plain,(
% 3.25/0.87    ~v1_xboole_0(sK3)),
% 3.25/0.87    inference(cnf_transformation,[],[f43])).
% 3.25/0.87  
% 3.25/0.87  fof(f10,axiom,(
% 3.25/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.25/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.87  
% 3.25/0.87  fof(f25,plain,(
% 3.25/0.87    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.87    inference(ennf_transformation,[],[f10])).
% 3.25/0.87  
% 3.25/0.87  fof(f56,plain,(
% 3.25/0.87    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.87    inference(cnf_transformation,[],[f25])).
% 3.25/0.87  
% 3.25/0.87  fof(f75,plain,(
% 3.25/0.87    ( ! [X4] : (r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2) | ~m1_subset_1(X4,sK3)) )),
% 3.25/0.87    inference(cnf_transformation,[],[f43])).
% 3.25/0.87  
% 3.25/0.87  fof(f69,plain,(
% 3.25/0.87    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK1(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.25/0.87    inference(cnf_transformation,[],[f39])).
% 3.25/0.87  
% 3.25/0.87  fof(f82,plain,(
% 3.25/0.87    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK1(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.25/0.87    inference(equality_resolution,[],[f69])).
% 3.25/0.87  
% 3.25/0.87  fof(f8,axiom,(
% 3.25/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.25/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.87  
% 3.25/0.87  fof(f23,plain,(
% 3.25/0.87    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.87    inference(ennf_transformation,[],[f8])).
% 3.25/0.87  
% 3.25/0.87  fof(f54,plain,(
% 3.25/0.87    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.87    inference(cnf_transformation,[],[f23])).
% 3.25/0.87  
% 3.25/0.87  fof(f5,axiom,(
% 3.25/0.87    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.25/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.87  
% 3.25/0.87  fof(f36,plain,(
% 3.25/0.87    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.25/0.87    inference(nnf_transformation,[],[f5])).
% 3.25/0.87  
% 3.25/0.87  fof(f50,plain,(
% 3.25/0.87    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.25/0.87    inference(cnf_transformation,[],[f36])).
% 3.25/0.87  
% 3.25/0.87  fof(f76,plain,(
% 3.25/0.87    ~r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2)),
% 3.25/0.87    inference(cnf_transformation,[],[f43])).
% 3.25/0.87  
% 3.25/0.87  cnf(c_21,plain,
% 3.25/0.87      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.25/0.87      | r2_hidden(sK1(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.25/0.87      | ~ v1_funct_1(X0)
% 3.25/0.87      | ~ v1_relat_1(X0) ),
% 3.25/0.87      inference(cnf_transformation,[],[f83]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_30,negated_conjecture,
% 3.25/0.87      ( v1_funct_1(sK5) ),
% 3.25/0.87      inference(cnf_transformation,[],[f72]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_1050,plain,
% 3.25/0.87      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.25/0.87      | r2_hidden(sK1(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.25/0.87      | ~ v1_relat_1(X0)
% 3.25/0.87      | sK5 != X0 ),
% 3.25/0.87      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_1051,plain,
% 3.25/0.87      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
% 3.25/0.87      | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5))
% 3.25/0.87      | ~ v1_relat_1(sK5) ),
% 3.25/0.87      inference(unflattening,[status(thm)],[c_1050]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_2379,plain,
% 3.25/0.87      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.25/0.87      | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
% 3.25/0.87      | v1_relat_1(sK5) != iProver_top ),
% 3.25/0.87      inference(predicate_to_equality,[status(thm)],[c_1051]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_28,negated_conjecture,
% 3.25/0.87      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.25/0.87      inference(cnf_transformation,[],[f74]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_37,plain,
% 3.25/0.87      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.25/0.87      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_1052,plain,
% 3.25/0.87      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.25/0.87      | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
% 3.25/0.87      | v1_relat_1(sK5) != iProver_top ),
% 3.25/0.87      inference(predicate_to_equality,[status(thm)],[c_1051]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_9,plain,
% 3.25/0.87      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.87      | v1_relat_1(X0) ),
% 3.25/0.87      inference(cnf_transformation,[],[f53]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_2706,plain,
% 3.25/0.87      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.25/0.87      | v1_relat_1(sK5) ),
% 3.25/0.87      inference(instantiation,[status(thm)],[c_9]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_2707,plain,
% 3.25/0.87      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.25/0.87      | v1_relat_1(sK5) = iProver_top ),
% 3.25/0.87      inference(predicate_to_equality,[status(thm)],[c_2706]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_3185,plain,
% 3.25/0.87      ( r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
% 3.25/0.87      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
% 3.25/0.87      inference(global_propositional_subsumption,
% 3.25/0.87                [status(thm)],
% 3.25/0.87                [c_2379,c_37,c_1052,c_2707]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_3186,plain,
% 3.25/0.87      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.25/0.87      | r2_hidden(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top ),
% 3.25/0.87      inference(renaming,[status(thm)],[c_3185]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_5,plain,
% 3.25/0.87      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.25/0.87      inference(cnf_transformation,[],[f49]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_2392,plain,
% 3.25/0.87      ( m1_subset_1(X0,X1) = iProver_top
% 3.25/0.87      | r2_hidden(X0,X1) != iProver_top ),
% 3.25/0.87      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_3193,plain,
% 3.25/0.87      ( m1_subset_1(sK1(k1_relat_1(sK5),X0,sK5),k1_relat_1(sK5)) = iProver_top
% 3.25/0.87      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
% 3.25/0.87      inference(superposition,[status(thm)],[c_3186,c_2392]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_18,plain,
% 3.25/0.87      ( ~ v1_funct_2(X0,X1,X2)
% 3.25/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.87      | k1_relset_1(X1,X2,X0) = X1
% 3.25/0.87      | k1_xboole_0 = X2 ),
% 3.25/0.87      inference(cnf_transformation,[],[f57]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_29,negated_conjecture,
% 3.25/0.87      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.25/0.87      inference(cnf_transformation,[],[f73]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_1317,plain,
% 3.25/0.87      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.87      | k1_relset_1(X1,X2,X0) = X1
% 3.25/0.87      | sK5 != X0
% 3.25/0.87      | sK4 != X2
% 3.25/0.87      | sK3 != X1
% 3.25/0.87      | k1_xboole_0 = X2 ),
% 3.25/0.87      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_1318,plain,
% 3.25/0.87      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.25/0.87      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.25/0.87      | k1_xboole_0 = sK4 ),
% 3.25/0.87      inference(unflattening,[status(thm)],[c_1317]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_1320,plain,
% 3.25/0.87      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.25/0.87      inference(global_propositional_subsumption,
% 3.25/0.87                [status(thm)],
% 3.25/0.87                [c_1318,c_28]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_2386,plain,
% 3.25/0.87      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.25/0.87      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_11,plain,
% 3.25/0.87      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.87      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.25/0.87      inference(cnf_transformation,[],[f55]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_2389,plain,
% 3.25/0.87      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.25/0.87      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.25/0.87      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_3282,plain,
% 3.25/0.87      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.25/0.87      inference(superposition,[status(thm)],[c_2386,c_2389]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_3516,plain,
% 3.25/0.87      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.25/0.87      inference(superposition,[status(thm)],[c_1320,c_3282]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_31,negated_conjecture,
% 3.25/0.87      ( ~ v1_xboole_0(sK4) ),
% 3.25/0.87      inference(cnf_transformation,[],[f71]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_2,plain,
% 3.25/0.87      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.25/0.87      inference(cnf_transformation,[],[f44]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_3,plain,
% 3.25/0.87      ( r1_tarski(k1_xboole_0,X0) ),
% 3.25/0.87      inference(cnf_transformation,[],[f47]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_4,plain,
% 3.25/0.87      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 3.25/0.87      inference(cnf_transformation,[],[f48]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_531,plain,
% 3.25/0.87      ( ~ r1_xboole_0(X0,X1)
% 3.25/0.87      | v1_xboole_0(X0)
% 3.25/0.87      | X1 != X2
% 3.25/0.87      | k1_xboole_0 != X0 ),
% 3.25/0.87      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_532,plain,
% 3.25/0.87      ( ~ r1_xboole_0(k1_xboole_0,X0) | v1_xboole_0(k1_xboole_0) ),
% 3.25/0.87      inference(unflattening,[status(thm)],[c_531]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_628,plain,
% 3.25/0.87      ( r2_hidden(sK0(X0,X1),X0)
% 3.25/0.87      | v1_xboole_0(k1_xboole_0)
% 3.25/0.87      | X2 != X1
% 3.25/0.87      | k1_xboole_0 != X0 ),
% 3.25/0.87      inference(resolution_lifted,[status(thm)],[c_2,c_532]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_629,plain,
% 3.25/0.87      ( r2_hidden(sK0(k1_xboole_0,X0),k1_xboole_0)
% 3.25/0.87      | v1_xboole_0(k1_xboole_0) ),
% 3.25/0.87      inference(unflattening,[status(thm)],[c_628]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_8,plain,
% 3.25/0.87      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.25/0.87      inference(cnf_transformation,[],[f52]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_513,plain,
% 3.25/0.87      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.25/0.87      inference(resolution_lifted,[status(thm)],[c_3,c_8]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_514,plain,
% 3.25/0.87      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.25/0.87      inference(unflattening,[status(thm)],[c_513]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_637,plain,
% 3.25/0.87      ( v1_xboole_0(k1_xboole_0) ),
% 3.25/0.87      inference(forward_subsumption_resolution,
% 3.25/0.87                [status(thm)],
% 3.25/0.87                [c_629,c_514]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_784,plain,
% 3.25/0.87      ( sK4 != k1_xboole_0 ),
% 3.25/0.87      inference(resolution_lifted,[status(thm)],[c_31,c_637]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_3613,plain,
% 3.25/0.87      ( k1_relat_1(sK5) = sK3 ),
% 3.25/0.87      inference(global_propositional_subsumption,
% 3.25/0.87                [status(thm)],
% 3.25/0.87                [c_3516,c_784]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_4658,plain,
% 3.25/0.87      ( m1_subset_1(sK1(sK3,X0,sK5),sK3) = iProver_top
% 3.25/0.87      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
% 3.25/0.87      inference(light_normalisation,[status(thm)],[c_3193,c_3613]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_19,plain,
% 3.25/0.87      ( ~ v1_funct_2(X0,X1,X2)
% 3.25/0.87      | ~ m1_subset_1(X3,X1)
% 3.25/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.87      | ~ v1_funct_1(X0)
% 3.25/0.87      | v1_xboole_0(X1)
% 3.25/0.87      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.25/0.87      inference(cnf_transformation,[],[f63]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_32,negated_conjecture,
% 3.25/0.87      ( ~ v1_xboole_0(sK3) ),
% 3.25/0.87      inference(cnf_transformation,[],[f70]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_739,plain,
% 3.25/0.87      ( ~ v1_funct_2(X0,X1,X2)
% 3.25/0.87      | ~ m1_subset_1(X3,X1)
% 3.25/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.87      | ~ v1_funct_1(X0)
% 3.25/0.87      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 3.25/0.87      | sK3 != X1 ),
% 3.25/0.87      inference(resolution_lifted,[status(thm)],[c_19,c_32]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_740,plain,
% 3.25/0.87      ( ~ v1_funct_2(X0,sK3,X1)
% 3.25/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 3.25/0.87      | ~ m1_subset_1(X2,sK3)
% 3.25/0.87      | ~ v1_funct_1(X0)
% 3.25/0.87      | k3_funct_2(sK3,X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.25/0.87      inference(unflattening,[status(thm)],[c_739]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_984,plain,
% 3.25/0.87      ( ~ v1_funct_2(X0,sK3,X1)
% 3.25/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 3.25/0.87      | ~ m1_subset_1(X2,sK3)
% 3.25/0.87      | k3_funct_2(sK3,X1,X0,X2) = k1_funct_1(X0,X2)
% 3.25/0.87      | sK5 != X0 ),
% 3.25/0.87      inference(resolution_lifted,[status(thm)],[c_740,c_30]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_985,plain,
% 3.25/0.87      ( ~ v1_funct_2(sK5,sK3,X0)
% 3.25/0.87      | ~ m1_subset_1(X1,sK3)
% 3.25/0.87      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
% 3.25/0.87      | k3_funct_2(sK3,X0,sK5,X1) = k1_funct_1(sK5,X1) ),
% 3.25/0.87      inference(unflattening,[status(thm)],[c_984]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_1418,plain,
% 3.25/0.87      ( ~ m1_subset_1(X0,sK3)
% 3.25/0.87      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 3.25/0.87      | k3_funct_2(sK3,X1,sK5,X0) = k1_funct_1(sK5,X0)
% 3.25/0.87      | sK5 != sK5
% 3.25/0.87      | sK4 != X1
% 3.25/0.87      | sK3 != sK3 ),
% 3.25/0.87      inference(resolution_lifted,[status(thm)],[c_29,c_985]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_1419,plain,
% 3.25/0.87      ( ~ m1_subset_1(X0,sK3)
% 3.25/0.87      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.25/0.87      | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
% 3.25/0.87      inference(unflattening,[status(thm)],[c_1418]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_1423,plain,
% 3.25/0.87      ( ~ m1_subset_1(X0,sK3)
% 3.25/0.87      | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
% 3.25/0.87      inference(global_propositional_subsumption,
% 3.25/0.87                [status(thm)],
% 3.25/0.87                [c_1419,c_28]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_2366,plain,
% 3.25/0.87      ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
% 3.25/0.87      | m1_subset_1(X0,sK3) != iProver_top ),
% 3.25/0.87      inference(predicate_to_equality,[status(thm)],[c_1423]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_4666,plain,
% 3.25/0.87      ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,X0,sK5)) = k1_funct_1(sK5,sK1(sK3,X0,sK5))
% 3.25/0.87      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
% 3.25/0.87      inference(superposition,[status(thm)],[c_4658,c_2366]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_3618,plain,
% 3.25/0.87      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.25/0.87      | r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top ),
% 3.25/0.87      inference(demodulation,[status(thm)],[c_3613,c_3186]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_12,plain,
% 3.25/0.87      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.87      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.25/0.87      inference(cnf_transformation,[],[f56]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_2388,plain,
% 3.25/0.87      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.25/0.87      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.25/0.87      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_4931,plain,
% 3.25/0.87      ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
% 3.25/0.87      | r2_hidden(sK1(sK3,X0,sK5),sK3) = iProver_top ),
% 3.25/0.87      inference(superposition,[status(thm)],[c_3618,c_2388]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_5204,plain,
% 3.25/0.87      ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
% 3.25/0.87      | m1_subset_1(sK1(sK3,X0,sK5),sK3) = iProver_top ),
% 3.25/0.87      inference(superposition,[status(thm)],[c_4931,c_2392]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_5236,plain,
% 3.25/0.87      ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,X0,sK5)) = k1_funct_1(sK5,sK1(sK3,X0,sK5))
% 3.25/0.87      | k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5) ),
% 3.25/0.87      inference(superposition,[status(thm)],[c_5204,c_2366]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_27,negated_conjecture,
% 3.25/0.87      ( ~ m1_subset_1(X0,sK3)
% 3.25/0.87      | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) ),
% 3.25/0.87      inference(cnf_transformation,[],[f75]) ).
% 3.25/0.87  
% 3.25/0.87  cnf(c_2387,plain,
% 3.25/0.87      ( m1_subset_1(X0,sK3) != iProver_top
% 3.25/0.87      | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) = iProver_top ),
% 3.25/0.87      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_5527,plain,
% 3.25/0.88      ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
% 3.25/0.88      | m1_subset_1(sK1(sK3,X0,sK5),sK3) != iProver_top
% 3.25/0.88      | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),sK2) = iProver_top ),
% 3.25/0.88      inference(superposition,[status(thm)],[c_5236,c_2387]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_5903,plain,
% 3.25/0.88      ( k2_relset_1(sK3,X0,sK5) = k2_relat_1(sK5)
% 3.25/0.88      | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),sK2) = iProver_top ),
% 3.25/0.88      inference(global_propositional_subsumption,
% 3.25/0.88                [status(thm)],
% 3.25/0.88                [c_5527,c_5204]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_20,plain,
% 3.25/0.88      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.25/0.88      | ~ r2_hidden(k1_funct_1(X0,sK1(k1_relat_1(X0),X1,X0)),X1)
% 3.25/0.88      | ~ v1_funct_1(X0)
% 3.25/0.88      | ~ v1_relat_1(X0) ),
% 3.25/0.88      inference(cnf_transformation,[],[f82]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_1065,plain,
% 3.25/0.88      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.25/0.88      | ~ r2_hidden(k1_funct_1(X0,sK1(k1_relat_1(X0),X1,X0)),X1)
% 3.25/0.88      | ~ v1_relat_1(X0)
% 3.25/0.88      | sK5 != X0 ),
% 3.25/0.88      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_1066,plain,
% 3.25/0.88      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0)))
% 3.25/0.88      | ~ r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0)
% 3.25/0.88      | ~ v1_relat_1(sK5) ),
% 3.25/0.88      inference(unflattening,[status(thm)],[c_1065]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_2378,plain,
% 3.25/0.88      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.25/0.88      | r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top
% 3.25/0.88      | v1_relat_1(sK5) != iProver_top ),
% 3.25/0.88      inference(predicate_to_equality,[status(thm)],[c_1066]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_1067,plain,
% 3.25/0.88      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.25/0.88      | r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top
% 3.25/0.88      | v1_relat_1(sK5) != iProver_top ),
% 3.25/0.88      inference(predicate_to_equality,[status(thm)],[c_1066]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_3123,plain,
% 3.25/0.88      ( r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top
% 3.25/0.88      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top ),
% 3.25/0.88      inference(global_propositional_subsumption,
% 3.25/0.88                [status(thm)],
% 3.25/0.88                [c_2378,c_37,c_1067,c_2707]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_3124,plain,
% 3.25/0.88      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 3.25/0.88      | r2_hidden(k1_funct_1(sK5,sK1(k1_relat_1(sK5),X0,sK5)),X0) != iProver_top ),
% 3.25/0.88      inference(renaming,[status(thm)],[c_3123]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_3619,plain,
% 3.25/0.88      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.25/0.88      | r2_hidden(k1_funct_1(sK5,sK1(sK3,X0,sK5)),X0) != iProver_top ),
% 3.25/0.88      inference(demodulation,[status(thm)],[c_3613,c_3124]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_5915,plain,
% 3.25/0.88      ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5)
% 3.25/0.88      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.25/0.88      inference(superposition,[status(thm)],[c_5903,c_3619]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_6044,plain,
% 3.25/0.88      ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5) ),
% 3.25/0.88      inference(forward_subsumption_resolution,
% 3.25/0.88                [status(thm)],
% 3.25/0.88                [c_5915,c_2388]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_10,plain,
% 3.25/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.88      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.25/0.88      inference(cnf_transformation,[],[f54]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_2390,plain,
% 3.25/0.88      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.25/0.88      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.25/0.88      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_6045,plain,
% 3.25/0.88      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top
% 3.25/0.88      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.25/0.88      inference(superposition,[status(thm)],[c_6044,c_2390]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_3278,plain,
% 3.25/0.88      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.25/0.88      inference(superposition,[status(thm)],[c_2386,c_2388]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_7,plain,
% 3.25/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.25/0.88      inference(cnf_transformation,[],[f50]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_253,plain,
% 3.25/0.88      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.25/0.88      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_254,plain,
% 3.25/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.25/0.88      inference(renaming,[status(thm)],[c_253]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_26,negated_conjecture,
% 3.25/0.88      ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) ),
% 3.25/0.88      inference(cnf_transformation,[],[f76]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_548,plain,
% 3.25/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.25/0.88      | k2_relset_1(sK3,sK4,sK5) != X0
% 3.25/0.88      | sK2 != X1 ),
% 3.25/0.88      inference(resolution_lifted,[status(thm)],[c_254,c_26]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_549,plain,
% 3.25/0.88      ( ~ m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK2)) ),
% 3.25/0.88      inference(unflattening,[status(thm)],[c_548]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_2382,plain,
% 3.25/0.88      ( m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK2)) != iProver_top ),
% 3.25/0.88      inference(predicate_to_equality,[status(thm)],[c_549]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_3479,plain,
% 3.25/0.88      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK2)) != iProver_top ),
% 3.25/0.88      inference(demodulation,[status(thm)],[c_3278,c_2382]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_6322,plain,
% 3.25/0.88      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.25/0.88      inference(global_propositional_subsumption,
% 3.25/0.88                [status(thm)],
% 3.25/0.88                [c_6045,c_3479]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_6423,plain,
% 3.25/0.88      ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK2,sK5)) = k1_funct_1(sK5,sK1(sK3,sK2,sK5)) ),
% 3.25/0.88      inference(superposition,[status(thm)],[c_4666,c_6322]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_7987,plain,
% 3.25/0.88      ( m1_subset_1(sK1(sK3,sK2,sK5),sK3) != iProver_top
% 3.25/0.88      | r2_hidden(k1_funct_1(sK5,sK1(sK3,sK2,sK5)),sK2) = iProver_top ),
% 3.25/0.88      inference(superposition,[status(thm)],[c_6423,c_2387]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_6327,plain,
% 3.25/0.88      ( r2_hidden(sK1(sK3,sK2,sK5),sK3) = iProver_top ),
% 3.25/0.88      inference(superposition,[status(thm)],[c_3618,c_6322]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_7554,plain,
% 3.25/0.88      ( m1_subset_1(sK1(sK3,sK2,sK5),sK3) = iProver_top ),
% 3.25/0.88      inference(superposition,[status(thm)],[c_6327,c_2392]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_8008,plain,
% 3.25/0.88      ( r2_hidden(k1_funct_1(sK5,sK1(sK3,sK2,sK5)),sK2) = iProver_top ),
% 3.25/0.88      inference(global_propositional_subsumption,
% 3.25/0.88                [status(thm)],
% 3.25/0.88                [c_7987,c_7554]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(c_8017,plain,
% 3.25/0.88      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.25/0.88      inference(superposition,[status(thm)],[c_8008,c_3619]) ).
% 3.25/0.88  
% 3.25/0.88  cnf(contradiction,plain,
% 3.25/0.88      ( $false ),
% 3.25/0.88      inference(minisat,[status(thm)],[c_8017,c_6045,c_3479]) ).
% 3.25/0.88  
% 3.25/0.88  
% 3.25/0.88  % SZS output end CNFRefutation for theBenchmark.p
% 3.25/0.88  
% 3.25/0.88  ------                               Statistics
% 3.25/0.88  
% 3.25/0.88  ------ General
% 3.25/0.88  
% 3.25/0.88  abstr_ref_over_cycles:                  0
% 3.25/0.88  abstr_ref_under_cycles:                 0
% 3.25/0.88  gc_basic_clause_elim:                   0
% 3.25/0.88  forced_gc_time:                         0
% 3.25/0.88  parsing_time:                           0.01
% 3.25/0.88  unif_index_cands_time:                  0.
% 3.25/0.88  unif_index_add_time:                    0.
% 3.25/0.88  orderings_time:                         0.
% 3.25/0.88  out_proof_time:                         0.009
% 3.25/0.88  total_time:                             0.245
% 3.25/0.88  num_of_symbols:                         57
% 3.25/0.88  num_of_terms:                           4899
% 3.25/0.88  
% 3.25/0.88  ------ Preprocessing
% 3.25/0.88  
% 3.25/0.88  num_of_splits:                          3
% 3.25/0.88  num_of_split_atoms:                     3
% 3.25/0.88  num_of_reused_defs:                     0
% 3.25/0.88  num_eq_ax_congr_red:                    18
% 3.25/0.88  num_of_sem_filtered_clauses:            1
% 3.25/0.88  num_of_subtypes:                        0
% 3.25/0.88  monotx_restored_types:                  0
% 3.25/0.88  sat_num_of_epr_types:                   0
% 3.25/0.88  sat_num_of_non_cyclic_types:            0
% 3.25/0.88  sat_guarded_non_collapsed_types:        0
% 3.25/0.88  num_pure_diseq_elim:                    0
% 3.25/0.88  simp_replaced_by:                       0
% 3.25/0.88  res_preprocessed:                       140
% 3.25/0.88  prep_upred:                             0
% 3.25/0.88  prep_unflattend:                        119
% 3.25/0.88  smt_new_axioms:                         0
% 3.25/0.88  pred_elim_cands:                        8
% 3.25/0.88  pred_elim:                              4
% 3.25/0.88  pred_elim_cl:                           -6
% 3.25/0.88  pred_elim_cycles:                       11
% 3.25/0.88  merged_defs:                            2
% 3.25/0.88  merged_defs_ncl:                        0
% 3.25/0.88  bin_hyper_res:                          2
% 3.25/0.88  prep_cycles:                            3
% 3.25/0.88  pred_elim_time:                         0.029
% 3.25/0.88  splitting_time:                         0.
% 3.25/0.88  sem_filter_time:                        0.
% 3.25/0.88  monotx_time:                            0.
% 3.25/0.88  subtype_inf_time:                       0.
% 3.25/0.88  
% 3.25/0.88  ------ Problem properties
% 3.25/0.88  
% 3.25/0.88  clauses:                                40
% 3.25/0.88  conjectures:                            2
% 3.25/0.88  epr:                                    5
% 3.25/0.88  horn:                                   26
% 3.25/0.88  ground:                                 10
% 3.25/0.88  unary:                                  7
% 3.25/0.88  binary:                                 13
% 3.25/0.88  lits:                                   112
% 3.25/0.88  lits_eq:                                40
% 3.25/0.88  fd_pure:                                0
% 3.25/0.88  fd_pseudo:                              0
% 3.25/0.88  fd_cond:                                4
% 3.25/0.88  fd_pseudo_cond:                         0
% 3.25/0.88  ac_symbols:                             0
% 3.25/0.88  
% 3.25/0.88  ------ Propositional Solver
% 3.25/0.88  
% 3.25/0.88  prop_solver_calls:                      24
% 3.25/0.88  prop_fast_solver_calls:                 1404
% 3.25/0.88  smt_solver_calls:                       0
% 3.25/0.88  smt_fast_solver_calls:                  0
% 3.25/0.88  prop_num_of_clauses:                    2665
% 3.25/0.88  prop_preprocess_simplified:             7059
% 3.25/0.88  prop_fo_subsumed:                       45
% 3.25/0.88  prop_solver_time:                       0.
% 3.25/0.88  smt_solver_time:                        0.
% 3.25/0.88  smt_fast_solver_time:                   0.
% 3.25/0.88  prop_fast_solver_time:                  0.
% 3.25/0.88  prop_unsat_core_time:                   0.
% 3.25/0.88  
% 3.25/0.88  ------ QBF
% 3.25/0.88  
% 3.25/0.88  qbf_q_res:                              0
% 3.25/0.88  qbf_num_tautologies:                    0
% 3.25/0.88  qbf_prep_cycles:                        0
% 3.25/0.88  
% 3.25/0.88  ------ BMC1
% 3.25/0.88  
% 3.25/0.88  bmc1_current_bound:                     -1
% 3.25/0.88  bmc1_last_solved_bound:                 -1
% 3.25/0.88  bmc1_unsat_core_size:                   -1
% 3.25/0.88  bmc1_unsat_core_parents_size:           -1
% 3.25/0.88  bmc1_merge_next_fun:                    0
% 3.25/0.88  bmc1_unsat_core_clauses_time:           0.
% 3.25/0.88  
% 3.25/0.88  ------ Instantiation
% 3.25/0.88  
% 3.25/0.88  inst_num_of_clauses:                    824
% 3.25/0.88  inst_num_in_passive:                    79
% 3.25/0.88  inst_num_in_active:                     407
% 3.25/0.88  inst_num_in_unprocessed:                338
% 3.25/0.88  inst_num_of_loops:                      540
% 3.25/0.88  inst_num_of_learning_restarts:          0
% 3.25/0.88  inst_num_moves_active_passive:          130
% 3.25/0.88  inst_lit_activity:                      0
% 3.25/0.88  inst_lit_activity_moves:                0
% 3.25/0.88  inst_num_tautologies:                   0
% 3.25/0.88  inst_num_prop_implied:                  0
% 3.25/0.88  inst_num_existing_simplified:           0
% 3.25/0.88  inst_num_eq_res_simplified:             0
% 3.25/0.88  inst_num_child_elim:                    0
% 3.25/0.88  inst_num_of_dismatching_blockings:      370
% 3.25/0.88  inst_num_of_non_proper_insts:           835
% 3.25/0.88  inst_num_of_duplicates:                 0
% 3.25/0.88  inst_inst_num_from_inst_to_res:         0
% 3.25/0.88  inst_dismatching_checking_time:         0.
% 3.25/0.88  
% 3.25/0.88  ------ Resolution
% 3.25/0.88  
% 3.25/0.88  res_num_of_clauses:                     0
% 3.25/0.88  res_num_in_passive:                     0
% 3.25/0.88  res_num_in_active:                      0
% 3.25/0.88  res_num_of_loops:                       143
% 3.25/0.88  res_forward_subset_subsumed:            72
% 3.25/0.88  res_backward_subset_subsumed:           0
% 3.25/0.88  res_forward_subsumed:                   1
% 3.25/0.88  res_backward_subsumed:                  1
% 3.25/0.88  res_forward_subsumption_resolution:     7
% 3.25/0.88  res_backward_subsumption_resolution:    1
% 3.25/0.88  res_clause_to_clause_subsumption:       501
% 3.25/0.88  res_orphan_elimination:                 0
% 3.25/0.88  res_tautology_del:                      97
% 3.25/0.88  res_num_eq_res_simplified:              0
% 3.25/0.88  res_num_sel_changes:                    0
% 3.25/0.88  res_moves_from_active_to_pass:          0
% 3.25/0.88  
% 3.25/0.88  ------ Superposition
% 3.25/0.88  
% 3.25/0.88  sup_time_total:                         0.
% 3.25/0.88  sup_time_generating:                    0.
% 3.25/0.88  sup_time_sim_full:                      0.
% 3.25/0.88  sup_time_sim_immed:                     0.
% 3.25/0.88  
% 3.25/0.88  sup_num_of_clauses:                     161
% 3.25/0.88  sup_num_in_active:                      98
% 3.25/0.88  sup_num_in_passive:                     63
% 3.25/0.88  sup_num_of_loops:                       107
% 3.25/0.88  sup_fw_superposition:                   63
% 3.25/0.88  sup_bw_superposition:                   125
% 3.25/0.88  sup_immediate_simplified:               23
% 3.25/0.88  sup_given_eliminated:                   0
% 3.25/0.88  comparisons_done:                       0
% 3.25/0.88  comparisons_avoided:                    9
% 3.25/0.88  
% 3.25/0.88  ------ Simplifications
% 3.25/0.88  
% 3.25/0.88  
% 3.25/0.88  sim_fw_subset_subsumed:                 15
% 3.25/0.88  sim_bw_subset_subsumed:                 8
% 3.25/0.88  sim_fw_subsumed:                        2
% 3.25/0.88  sim_bw_subsumed:                        0
% 3.25/0.88  sim_fw_subsumption_res:                 2
% 3.25/0.88  sim_bw_subsumption_res:                 0
% 3.25/0.88  sim_tautology_del:                      1
% 3.25/0.88  sim_eq_tautology_del:                   0
% 3.25/0.88  sim_eq_res_simp:                        0
% 3.25/0.88  sim_fw_demodulated:                     0
% 3.25/0.88  sim_bw_demodulated:                     7
% 3.25/0.88  sim_light_normalised:                   13
% 3.25/0.88  sim_joinable_taut:                      0
% 3.25/0.88  sim_joinable_simp:                      0
% 3.25/0.88  sim_ac_normalised:                      0
% 3.25/0.88  sim_smt_subsumption:                    0
% 3.25/0.88  
%------------------------------------------------------------------------------
