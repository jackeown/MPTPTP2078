%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:35 EST 2020

% Result     : Theorem 7.70s
% Output     : CNFRefutation 7.70s
% Verified   : 
% Statistics : Number of formulae       :  235 (4934 expanded)
%              Number of clauses        :  152 (1750 expanded)
%              Number of leaves         :   31 (1291 expanded)
%              Depth                    :   32
%              Number of atoms          :  598 (20061 expanded)
%              Number of equality atoms :  266 (4747 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :   12 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f58,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f21,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
              | ~ m1_subset_1(X3,X1) )
          & k1_xboole_0 != k1_relset_1(X0,X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(X0,X1,sK6))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k1_relset_1(X0,X1,sK6)
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(X0,sK5,X2))
                | ~ m1_subset_1(X3,sK5) )
            & k1_xboole_0 != k1_relset_1(X0,sK5,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK5))) )
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k1_relset_1(X0,X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK4,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(sK4,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK4,sK5,sK6))
        | ~ m1_subset_1(X3,sK5) )
    & k1_xboole_0 != k1_relset_1(sK4,sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f55,f54,f53])).

fof(f88,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f56])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f45])).

fof(f49,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f49,f48,f47])).

fof(f63,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f63])).

fof(f5,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK4,sK5,sK6))
      | ~ m1_subset_1(X3,sK5) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,(
    k1_xboole_0 != k1_relset_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1537,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1512,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1525,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3275,plain,
    ( r2_hidden(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1512,c_1525])).

cnf(c_36,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1788,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | r2_hidden(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1789,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | r2_hidden(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1788])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2419,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2420,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2419])).

cnf(c_3595,plain,
    ( r2_hidden(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3275,c_36,c_1789,c_2420])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1530,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3600,plain,
    ( r2_hidden(X0,k3_tarski(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_1530])).

cnf(c_10,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3606,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3600,c_10])).

cnf(c_3690,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_zfmisc_1(sK4,sK5))) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3606,c_1530])).

cnf(c_3975,plain,
    ( r2_hidden(X0,k3_tarski(k2_zfmisc_1(sK4,sK5))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3606,c_3690])).

cnf(c_6666,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3975,c_1530])).

cnf(c_8382,plain,
    ( r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
    | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top
    | r2_hidden(sK6,k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_6666])).

cnf(c_8792,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5))))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
    | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8382,c_1530])).

cnf(c_9516,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))))) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
    | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8792,c_1530])).

cnf(c_11097,plain,
    ( r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
    | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top
    | r2_hidden(sK6,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_9516])).

cnf(c_11404,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5))))))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
    | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_11097,c_1530])).

cnf(c_12039,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))))))) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
    | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_11404,c_1530])).

cnf(c_12710,plain,
    ( r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
    | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top
    | r2_hidden(sK6,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_12039])).

cnf(c_14260,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5))))))))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
    | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12710,c_1530])).

cnf(c_14612,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))))))))) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
    | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_14260,c_1530])).

cnf(c_15796,plain,
    ( r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
    | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top
    | r2_hidden(sK6,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))))))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_14612])).

cnf(c_16125,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5))))))))))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
    | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_15796,c_1530])).

cnf(c_15,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1759,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1760,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1814,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k3_relset_1(sK4,sK5,sK6) = k4_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1817,plain,
    ( m1_subset_1(k3_relset_1(sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1818,plain,
    ( m1_subset_1(k3_relset_1(sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1817])).

cnf(c_1877,plain,
    ( r1_tarski(k3_relset_1(sK4,sK5,sK6),k2_zfmisc_1(sK5,sK4))
    | ~ m1_subset_1(k3_relset_1(sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1878,plain,
    ( r1_tarski(k3_relset_1(sK4,sK5,sK6),k2_zfmisc_1(sK5,sK4)) = iProver_top
    | m1_subset_1(k3_relset_1(sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1877])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_261,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_318,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_261])).

cnf(c_1839,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_2351,plain,
    ( ~ r1_tarski(sK6,k2_zfmisc_1(sK4,sK5))
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1839])).

cnf(c_2352,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2351])).

cnf(c_20,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2382,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2383,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2382])).

cnf(c_2585,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2586,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2585])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2626,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_xboole_0(k1_relat_1(sK6))
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2627,plain,
    ( v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(k1_relat_1(sK6)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2626])).

cnf(c_821,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2114,plain,
    ( X0 != X1
    | X0 = k3_relset_1(sK4,sK5,sK6)
    | k3_relset_1(sK4,sK5,sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_2959,plain,
    ( X0 = k3_relset_1(sK4,sK5,sK6)
    | X0 != k4_relat_1(sK6)
    | k3_relset_1(sK4,sK5,sK6) != k4_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2114])).

cnf(c_3589,plain,
    ( k3_relset_1(sK4,sK5,sK6) != k4_relat_1(sK6)
    | k4_relat_1(sK6) = k3_relset_1(sK4,sK5,sK6)
    | k4_relat_1(sK6) != k4_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2959])).

cnf(c_820,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3590,plain,
    ( k4_relat_1(sK6) = k4_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3639,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3640,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3639])).

cnf(c_827,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1975,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK5,sK4))
    | ~ r1_tarski(k3_relset_1(sK4,sK5,sK6),k2_zfmisc_1(sK5,sK4))
    | X0 != k3_relset_1(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_3718,plain,
    ( ~ r1_tarski(k3_relset_1(sK4,sK5,sK6),k2_zfmisc_1(sK5,sK4))
    | r1_tarski(k4_relat_1(sK6),k2_zfmisc_1(sK5,sK4))
    | k4_relat_1(sK6) != k3_relset_1(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1975])).

cnf(c_3724,plain,
    ( k4_relat_1(sK6) != k3_relset_1(sK4,sK5,sK6)
    | r1_tarski(k3_relset_1(sK4,sK5,sK6),k2_zfmisc_1(sK5,sK4)) != iProver_top
    | r1_tarski(k4_relat_1(sK6),k2_zfmisc_1(sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3718])).

cnf(c_1516,plain,
    ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2614,plain,
    ( k3_relset_1(sK4,sK5,sK6) = k4_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1512,c_1516])).

cnf(c_1519,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4020,plain,
    ( m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2614,c_1519])).

cnf(c_4602,plain,
    ( m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4020,c_36])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1517,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4613,plain,
    ( k2_relset_1(sK5,sK4,k4_relat_1(sK6)) = k2_relat_1(k4_relat_1(sK6)) ),
    inference(superposition,[status(thm)],[c_4602,c_1517])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1515,plain,
    ( k2_relset_1(X0,X1,k3_relset_1(X1,X0,X2)) = k1_relset_1(X1,X0,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3138,plain,
    ( k2_relset_1(sK5,sK4,k3_relset_1(sK4,sK5,sK6)) = k1_relset_1(sK4,sK5,sK6) ),
    inference(superposition,[status(thm)],[c_1512,c_1515])).

cnf(c_3140,plain,
    ( k2_relset_1(sK5,sK4,k4_relat_1(sK6)) = k1_relset_1(sK4,sK5,sK6) ),
    inference(light_normalisation,[status(thm)],[c_3138,c_2614])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1518,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3153,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1512,c_1518])).

cnf(c_3685,plain,
    ( k2_relset_1(sK5,sK4,k4_relat_1(sK6)) = k1_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_3140,c_3153])).

cnf(c_4618,plain,
    ( k2_relat_1(k4_relat_1(sK6)) = k1_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_4613,c_3685])).

cnf(c_19,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1522,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4881,plain,
    ( v1_xboole_0(k4_relat_1(sK6)) != iProver_top
    | v1_xboole_0(k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4618,c_1522])).

cnf(c_4612,plain,
    ( k1_relset_1(sK5,sK4,k4_relat_1(sK6)) = k1_relat_1(k4_relat_1(sK6)) ),
    inference(superposition,[status(thm)],[c_4602,c_1518])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1514,plain,
    ( k1_relset_1(X0,X1,k3_relset_1(X1,X0,X2)) = k2_relset_1(X1,X0,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2510,plain,
    ( k1_relset_1(sK5,sK4,k3_relset_1(sK4,sK5,sK6)) = k2_relset_1(sK4,sK5,sK6) ),
    inference(superposition,[status(thm)],[c_1512,c_1514])).

cnf(c_2745,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1512,c_1517])).

cnf(c_2896,plain,
    ( k1_relset_1(sK5,sK4,k4_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_2510,c_2614,c_2745])).

cnf(c_4621,plain,
    ( k1_relat_1(k4_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_4612,c_2896])).

cnf(c_1520,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4884,plain,
    ( v1_relat_1(k4_relat_1(sK6)) != iProver_top
    | v1_xboole_0(k4_relat_1(sK6)) = iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4621,c_1520])).

cnf(c_7462,plain,
    ( ~ r1_tarski(k4_relat_1(sK6),k2_zfmisc_1(sK5,sK4))
    | ~ v1_relat_1(k2_zfmisc_1(sK5,sK4))
    | v1_relat_1(k4_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1839])).

cnf(c_7463,plain,
    ( r1_tarski(k4_relat_1(sK6),k2_zfmisc_1(sK5,sK4)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK5,sK4)) != iProver_top
    | v1_relat_1(k4_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7462])).

cnf(c_4614,plain,
    ( k3_relset_1(sK5,sK4,k4_relat_1(sK6)) = k4_relat_1(k4_relat_1(sK6)) ),
    inference(superposition,[status(thm)],[c_4602,c_1516])).

cnf(c_4962,plain,
    ( m1_subset_1(k4_relat_1(k4_relat_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top
    | m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4614,c_1519])).

cnf(c_5610,plain,
    ( m1_subset_1(k4_relat_1(k4_relat_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4962,c_36,c_4020])).

cnf(c_22,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_18,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_428,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_18])).

cnf(c_1508,plain,
    ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_5617,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k4_relat_1(sK6))),sK5) = iProver_top
    | v1_relat_1(k4_relat_1(k4_relat_1(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5610,c_1508])).

cnf(c_5621,plain,
    ( k2_relset_1(sK4,sK5,k4_relat_1(k4_relat_1(sK6))) = k2_relat_1(k4_relat_1(k4_relat_1(sK6))) ),
    inference(superposition,[status(thm)],[c_5610,c_1517])).

cnf(c_4610,plain,
    ( k2_relset_1(sK4,sK5,k3_relset_1(sK5,sK4,k4_relat_1(sK6))) = k1_relset_1(sK5,sK4,k4_relat_1(sK6)) ),
    inference(superposition,[status(thm)],[c_4602,c_1515])).

cnf(c_4627,plain,
    ( k2_relset_1(sK4,sK5,k4_relat_1(k4_relat_1(sK6))) = k1_relset_1(sK5,sK4,k4_relat_1(sK6)) ),
    inference(light_normalisation,[status(thm)],[c_4610,c_4614])).

cnf(c_4629,plain,
    ( k2_relset_1(sK4,sK5,k4_relat_1(k4_relat_1(sK6))) = k2_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_4627,c_2896])).

cnf(c_5626,plain,
    ( k2_relat_1(k4_relat_1(k4_relat_1(sK6))) = k2_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_5621,c_4629])).

cnf(c_5639,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
    | v1_relat_1(k4_relat_1(k4_relat_1(sK6))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5617,c_5626])).

cnf(c_1865,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1512,c_1508])).

cnf(c_6858,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5639,c_36,c_1760,c_1865,c_2352,c_2383])).

cnf(c_1524,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3274,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1524,c_1525])).

cnf(c_1527,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_16295,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3274,c_1527])).

cnf(c_16304,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(k1_zfmisc_1(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16295,c_1530])).

cnf(c_16321,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16304,c_10])).

cnf(c_16460,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6858,c_16321])).

cnf(c_16518,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6)),sK5) = iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1537,c_16460])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1526,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_16593,plain,
    ( m1_subset_1(sK0(k2_relat_1(sK6)),sK5) = iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16518,c_1526])).

cnf(c_29,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,k2_relset_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1513,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,k2_relset_1(sK4,sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1989,plain,
    ( m1_subset_1(sK0(k2_relset_1(sK4,sK5,sK6)),sK5) != iProver_top
    | v1_xboole_0(k2_relset_1(sK4,sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1537,c_1513])).

cnf(c_2882,plain,
    ( m1_subset_1(sK0(k2_relat_1(sK6)),sK5) != iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2745,c_1989])).

cnf(c_16658,plain,
    ( v1_xboole_0(k2_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16593,c_2882])).

cnf(c_16795,plain,
    ( r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16125,c_31,c_36,c_1760,c_1814,c_1818,c_1878,c_2352,c_2383,c_2586,c_2627,c_2882,c_3589,c_3590,c_3640,c_3724,c_4881,c_4884,c_7463,c_16593])).

cnf(c_16802,plain,
    ( v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1537,c_16795])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1535,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1534,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2596,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1534])).

cnf(c_16930,plain,
    ( sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16802,c_2596])).

cnf(c_18441,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16930,c_4881])).

cnf(c_16673,plain,
    ( v1_relat_1(k4_relat_1(sK6)) != iProver_top
    | v1_xboole_0(k4_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16658,c_4884])).

cnf(c_22329,plain,
    ( v1_xboole_0(k4_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16673,c_31,c_36,c_1814,c_1818,c_1878,c_2586,c_2882,c_3589,c_3590,c_3724,c_4884,c_7463,c_16593])).

cnf(c_22333,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22329,c_16930])).

cnf(c_22364,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18441,c_22333])).

cnf(c_22377,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_22364,c_2596])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != k1_relset_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3495,plain,
    ( k1_relat_1(sK6) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3153,c_30])).

cnf(c_18455,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16930,c_3495])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22377,c_18455])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n010.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 17:03:44 EST 2020
% 0.17/0.32  % CPUTime    : 
% 0.17/0.33  % Running in FOF mode
% 7.70/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.70/1.48  
% 7.70/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.70/1.48  
% 7.70/1.48  ------  iProver source info
% 7.70/1.48  
% 7.70/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.70/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.70/1.48  git: non_committed_changes: false
% 7.70/1.48  git: last_make_outside_of_git: false
% 7.70/1.48  
% 7.70/1.48  ------ 
% 7.70/1.48  
% 7.70/1.48  ------ Input Options
% 7.70/1.48  
% 7.70/1.48  --out_options                           all
% 7.70/1.48  --tptp_safe_out                         true
% 7.70/1.48  --problem_path                          ""
% 7.70/1.48  --include_path                          ""
% 7.70/1.48  --clausifier                            res/vclausify_rel
% 7.70/1.48  --clausifier_options                    --mode clausify
% 7.70/1.48  --stdin                                 false
% 7.70/1.48  --stats_out                             all
% 7.70/1.48  
% 7.70/1.48  ------ General Options
% 7.70/1.48  
% 7.70/1.48  --fof                                   false
% 7.70/1.48  --time_out_real                         305.
% 7.70/1.48  --time_out_virtual                      -1.
% 7.70/1.48  --symbol_type_check                     false
% 7.70/1.48  --clausify_out                          false
% 7.70/1.48  --sig_cnt_out                           false
% 7.70/1.48  --trig_cnt_out                          false
% 7.70/1.48  --trig_cnt_out_tolerance                1.
% 7.70/1.48  --trig_cnt_out_sk_spl                   false
% 7.70/1.48  --abstr_cl_out                          false
% 7.70/1.48  
% 7.70/1.48  ------ Global Options
% 7.70/1.48  
% 7.70/1.48  --schedule                              default
% 7.70/1.48  --add_important_lit                     false
% 7.70/1.48  --prop_solver_per_cl                    1000
% 7.70/1.48  --min_unsat_core                        false
% 7.70/1.48  --soft_assumptions                      false
% 7.70/1.48  --soft_lemma_size                       3
% 7.70/1.48  --prop_impl_unit_size                   0
% 7.70/1.48  --prop_impl_unit                        []
% 7.70/1.48  --share_sel_clauses                     true
% 7.70/1.48  --reset_solvers                         false
% 7.70/1.48  --bc_imp_inh                            [conj_cone]
% 7.70/1.48  --conj_cone_tolerance                   3.
% 7.70/1.48  --extra_neg_conj                        none
% 7.70/1.48  --large_theory_mode                     true
% 7.70/1.48  --prolific_symb_bound                   200
% 7.70/1.48  --lt_threshold                          2000
% 7.70/1.48  --clause_weak_htbl                      true
% 7.70/1.48  --gc_record_bc_elim                     false
% 7.70/1.48  
% 7.70/1.48  ------ Preprocessing Options
% 7.70/1.48  
% 7.70/1.48  --preprocessing_flag                    true
% 7.70/1.48  --time_out_prep_mult                    0.1
% 7.70/1.48  --splitting_mode                        input
% 7.70/1.48  --splitting_grd                         true
% 7.70/1.48  --splitting_cvd                         false
% 7.70/1.48  --splitting_cvd_svl                     false
% 7.70/1.48  --splitting_nvd                         32
% 7.70/1.48  --sub_typing                            true
% 7.70/1.48  --prep_gs_sim                           true
% 7.70/1.48  --prep_unflatten                        true
% 7.70/1.48  --prep_res_sim                          true
% 7.70/1.48  --prep_upred                            true
% 7.70/1.48  --prep_sem_filter                       exhaustive
% 7.70/1.48  --prep_sem_filter_out                   false
% 7.70/1.48  --pred_elim                             true
% 7.70/1.48  --res_sim_input                         true
% 7.70/1.48  --eq_ax_congr_red                       true
% 7.70/1.48  --pure_diseq_elim                       true
% 7.70/1.48  --brand_transform                       false
% 7.70/1.48  --non_eq_to_eq                          false
% 7.70/1.48  --prep_def_merge                        true
% 7.70/1.48  --prep_def_merge_prop_impl              false
% 7.70/1.48  --prep_def_merge_mbd                    true
% 7.70/1.48  --prep_def_merge_tr_red                 false
% 7.70/1.48  --prep_def_merge_tr_cl                  false
% 7.70/1.48  --smt_preprocessing                     true
% 7.70/1.48  --smt_ac_axioms                         fast
% 7.70/1.48  --preprocessed_out                      false
% 7.70/1.48  --preprocessed_stats                    false
% 7.70/1.48  
% 7.70/1.48  ------ Abstraction refinement Options
% 7.70/1.48  
% 7.70/1.48  --abstr_ref                             []
% 7.70/1.48  --abstr_ref_prep                        false
% 7.70/1.48  --abstr_ref_until_sat                   false
% 7.70/1.48  --abstr_ref_sig_restrict                funpre
% 7.70/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.70/1.48  --abstr_ref_under                       []
% 7.70/1.48  
% 7.70/1.48  ------ SAT Options
% 7.70/1.48  
% 7.70/1.48  --sat_mode                              false
% 7.70/1.48  --sat_fm_restart_options                ""
% 7.70/1.48  --sat_gr_def                            false
% 7.70/1.48  --sat_epr_types                         true
% 7.70/1.48  --sat_non_cyclic_types                  false
% 7.70/1.48  --sat_finite_models                     false
% 7.70/1.48  --sat_fm_lemmas                         false
% 7.70/1.48  --sat_fm_prep                           false
% 7.70/1.48  --sat_fm_uc_incr                        true
% 7.70/1.48  --sat_out_model                         small
% 7.70/1.48  --sat_out_clauses                       false
% 7.70/1.48  
% 7.70/1.48  ------ QBF Options
% 7.70/1.48  
% 7.70/1.48  --qbf_mode                              false
% 7.70/1.48  --qbf_elim_univ                         false
% 7.70/1.48  --qbf_dom_inst                          none
% 7.70/1.48  --qbf_dom_pre_inst                      false
% 7.70/1.48  --qbf_sk_in                             false
% 7.70/1.48  --qbf_pred_elim                         true
% 7.70/1.48  --qbf_split                             512
% 7.70/1.48  
% 7.70/1.48  ------ BMC1 Options
% 7.70/1.48  
% 7.70/1.48  --bmc1_incremental                      false
% 7.70/1.48  --bmc1_axioms                           reachable_all
% 7.70/1.48  --bmc1_min_bound                        0
% 7.70/1.48  --bmc1_max_bound                        -1
% 7.70/1.48  --bmc1_max_bound_default                -1
% 7.70/1.48  --bmc1_symbol_reachability              true
% 7.70/1.48  --bmc1_property_lemmas                  false
% 7.70/1.48  --bmc1_k_induction                      false
% 7.70/1.48  --bmc1_non_equiv_states                 false
% 7.70/1.48  --bmc1_deadlock                         false
% 7.70/1.48  --bmc1_ucm                              false
% 7.70/1.48  --bmc1_add_unsat_core                   none
% 7.70/1.48  --bmc1_unsat_core_children              false
% 7.70/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.70/1.48  --bmc1_out_stat                         full
% 7.70/1.48  --bmc1_ground_init                      false
% 7.70/1.48  --bmc1_pre_inst_next_state              false
% 7.70/1.48  --bmc1_pre_inst_state                   false
% 7.70/1.48  --bmc1_pre_inst_reach_state             false
% 7.70/1.48  --bmc1_out_unsat_core                   false
% 7.70/1.48  --bmc1_aig_witness_out                  false
% 7.70/1.48  --bmc1_verbose                          false
% 7.70/1.48  --bmc1_dump_clauses_tptp                false
% 7.70/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.70/1.48  --bmc1_dump_file                        -
% 7.70/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.70/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.70/1.48  --bmc1_ucm_extend_mode                  1
% 7.70/1.48  --bmc1_ucm_init_mode                    2
% 7.70/1.48  --bmc1_ucm_cone_mode                    none
% 7.70/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.70/1.48  --bmc1_ucm_relax_model                  4
% 7.70/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.70/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.70/1.48  --bmc1_ucm_layered_model                none
% 7.70/1.48  --bmc1_ucm_max_lemma_size               10
% 7.70/1.48  
% 7.70/1.48  ------ AIG Options
% 7.70/1.48  
% 7.70/1.48  --aig_mode                              false
% 7.70/1.48  
% 7.70/1.48  ------ Instantiation Options
% 7.70/1.48  
% 7.70/1.48  --instantiation_flag                    true
% 7.70/1.48  --inst_sos_flag                         false
% 7.70/1.48  --inst_sos_phase                        true
% 7.70/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.70/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.70/1.48  --inst_lit_sel_side                     num_symb
% 7.70/1.48  --inst_solver_per_active                1400
% 7.70/1.48  --inst_solver_calls_frac                1.
% 7.70/1.48  --inst_passive_queue_type               priority_queues
% 7.70/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.70/1.48  --inst_passive_queues_freq              [25;2]
% 7.70/1.48  --inst_dismatching                      true
% 7.70/1.48  --inst_eager_unprocessed_to_passive     true
% 7.70/1.48  --inst_prop_sim_given                   true
% 7.70/1.48  --inst_prop_sim_new                     false
% 7.70/1.48  --inst_subs_new                         false
% 7.70/1.48  --inst_eq_res_simp                      false
% 7.70/1.48  --inst_subs_given                       false
% 7.70/1.48  --inst_orphan_elimination               true
% 7.70/1.48  --inst_learning_loop_flag               true
% 7.70/1.48  --inst_learning_start                   3000
% 7.70/1.48  --inst_learning_factor                  2
% 7.70/1.48  --inst_start_prop_sim_after_learn       3
% 7.70/1.48  --inst_sel_renew                        solver
% 7.70/1.48  --inst_lit_activity_flag                true
% 7.70/1.48  --inst_restr_to_given                   false
% 7.70/1.48  --inst_activity_threshold               500
% 7.70/1.48  --inst_out_proof                        true
% 7.70/1.48  
% 7.70/1.48  ------ Resolution Options
% 7.70/1.48  
% 7.70/1.48  --resolution_flag                       true
% 7.70/1.48  --res_lit_sel                           adaptive
% 7.70/1.48  --res_lit_sel_side                      none
% 7.70/1.48  --res_ordering                          kbo
% 7.70/1.48  --res_to_prop_solver                    active
% 7.70/1.48  --res_prop_simpl_new                    false
% 7.70/1.48  --res_prop_simpl_given                  true
% 7.70/1.48  --res_passive_queue_type                priority_queues
% 7.70/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.70/1.48  --res_passive_queues_freq               [15;5]
% 7.70/1.48  --res_forward_subs                      full
% 7.70/1.48  --res_backward_subs                     full
% 7.70/1.48  --res_forward_subs_resolution           true
% 7.70/1.48  --res_backward_subs_resolution          true
% 7.70/1.48  --res_orphan_elimination                true
% 7.70/1.48  --res_time_limit                        2.
% 7.70/1.48  --res_out_proof                         true
% 7.70/1.48  
% 7.70/1.48  ------ Superposition Options
% 7.70/1.48  
% 7.70/1.48  --superposition_flag                    true
% 7.70/1.48  --sup_passive_queue_type                priority_queues
% 7.70/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.70/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.70/1.48  --demod_completeness_check              fast
% 7.70/1.48  --demod_use_ground                      true
% 7.70/1.48  --sup_to_prop_solver                    passive
% 7.70/1.48  --sup_prop_simpl_new                    true
% 7.70/1.48  --sup_prop_simpl_given                  true
% 7.70/1.48  --sup_fun_splitting                     false
% 7.70/1.48  --sup_smt_interval                      50000
% 7.70/1.48  
% 7.70/1.48  ------ Superposition Simplification Setup
% 7.70/1.48  
% 7.70/1.48  --sup_indices_passive                   []
% 7.70/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.70/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.70/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.70/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.70/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.70/1.48  --sup_full_bw                           [BwDemod]
% 7.70/1.48  --sup_immed_triv                        [TrivRules]
% 7.70/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.70/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.70/1.48  --sup_immed_bw_main                     []
% 7.70/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.70/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.70/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.70/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.70/1.48  
% 7.70/1.48  ------ Combination Options
% 7.70/1.48  
% 7.70/1.48  --comb_res_mult                         3
% 7.70/1.48  --comb_sup_mult                         2
% 7.70/1.48  --comb_inst_mult                        10
% 7.70/1.48  
% 7.70/1.48  ------ Debug Options
% 7.70/1.48  
% 7.70/1.48  --dbg_backtrace                         false
% 7.70/1.48  --dbg_dump_prop_clauses                 false
% 7.70/1.48  --dbg_dump_prop_clauses_file            -
% 7.70/1.48  --dbg_out_stat                          false
% 7.70/1.48  ------ Parsing...
% 7.70/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.70/1.48  
% 7.70/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.70/1.48  
% 7.70/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.70/1.48  
% 7.70/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.48  ------ Proving...
% 7.70/1.48  ------ Problem Properties 
% 7.70/1.48  
% 7.70/1.48  
% 7.70/1.48  clauses                                 32
% 7.70/1.48  conjectures                             5
% 7.70/1.48  EPR                                     8
% 7.70/1.48  Horn                                    28
% 7.70/1.48  unary                                   8
% 7.70/1.48  binary                                  15
% 7.70/1.48  lits                                    66
% 7.70/1.48  lits eq                                 11
% 7.70/1.48  fd_pure                                 0
% 7.70/1.48  fd_pseudo                               0
% 7.70/1.48  fd_cond                                 0
% 7.70/1.48  fd_pseudo_cond                          4
% 7.70/1.48  AC symbols                              0
% 7.70/1.48  
% 7.70/1.48  ------ Schedule dynamic 5 is on 
% 7.70/1.48  
% 7.70/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.70/1.48  
% 7.70/1.48  
% 7.70/1.48  ------ 
% 7.70/1.48  Current options:
% 7.70/1.48  ------ 
% 7.70/1.48  
% 7.70/1.48  ------ Input Options
% 7.70/1.48  
% 7.70/1.48  --out_options                           all
% 7.70/1.48  --tptp_safe_out                         true
% 7.70/1.48  --problem_path                          ""
% 7.70/1.48  --include_path                          ""
% 7.70/1.48  --clausifier                            res/vclausify_rel
% 7.70/1.48  --clausifier_options                    --mode clausify
% 7.70/1.48  --stdin                                 false
% 7.70/1.48  --stats_out                             all
% 7.70/1.48  
% 7.70/1.48  ------ General Options
% 7.70/1.48  
% 7.70/1.48  --fof                                   false
% 7.70/1.48  --time_out_real                         305.
% 7.70/1.48  --time_out_virtual                      -1.
% 7.70/1.48  --symbol_type_check                     false
% 7.70/1.48  --clausify_out                          false
% 7.70/1.48  --sig_cnt_out                           false
% 7.70/1.48  --trig_cnt_out                          false
% 7.70/1.48  --trig_cnt_out_tolerance                1.
% 7.70/1.48  --trig_cnt_out_sk_spl                   false
% 7.70/1.48  --abstr_cl_out                          false
% 7.70/1.48  
% 7.70/1.48  ------ Global Options
% 7.70/1.48  
% 7.70/1.48  --schedule                              default
% 7.70/1.48  --add_important_lit                     false
% 7.70/1.48  --prop_solver_per_cl                    1000
% 7.70/1.48  --min_unsat_core                        false
% 7.70/1.48  --soft_assumptions                      false
% 7.70/1.48  --soft_lemma_size                       3
% 7.70/1.48  --prop_impl_unit_size                   0
% 7.70/1.48  --prop_impl_unit                        []
% 7.70/1.48  --share_sel_clauses                     true
% 7.70/1.48  --reset_solvers                         false
% 7.70/1.48  --bc_imp_inh                            [conj_cone]
% 7.70/1.48  --conj_cone_tolerance                   3.
% 7.70/1.48  --extra_neg_conj                        none
% 7.70/1.48  --large_theory_mode                     true
% 7.70/1.48  --prolific_symb_bound                   200
% 7.70/1.48  --lt_threshold                          2000
% 7.70/1.48  --clause_weak_htbl                      true
% 7.70/1.48  --gc_record_bc_elim                     false
% 7.70/1.48  
% 7.70/1.48  ------ Preprocessing Options
% 7.70/1.48  
% 7.70/1.48  --preprocessing_flag                    true
% 7.70/1.48  --time_out_prep_mult                    0.1
% 7.70/1.48  --splitting_mode                        input
% 7.70/1.48  --splitting_grd                         true
% 7.70/1.48  --splitting_cvd                         false
% 7.70/1.48  --splitting_cvd_svl                     false
% 7.70/1.48  --splitting_nvd                         32
% 7.70/1.48  --sub_typing                            true
% 7.70/1.48  --prep_gs_sim                           true
% 7.70/1.48  --prep_unflatten                        true
% 7.70/1.48  --prep_res_sim                          true
% 7.70/1.48  --prep_upred                            true
% 7.70/1.48  --prep_sem_filter                       exhaustive
% 7.70/1.48  --prep_sem_filter_out                   false
% 7.70/1.48  --pred_elim                             true
% 7.70/1.48  --res_sim_input                         true
% 7.70/1.48  --eq_ax_congr_red                       true
% 7.70/1.48  --pure_diseq_elim                       true
% 7.70/1.48  --brand_transform                       false
% 7.70/1.48  --non_eq_to_eq                          false
% 7.70/1.48  --prep_def_merge                        true
% 7.70/1.48  --prep_def_merge_prop_impl              false
% 7.70/1.48  --prep_def_merge_mbd                    true
% 7.70/1.48  --prep_def_merge_tr_red                 false
% 7.70/1.48  --prep_def_merge_tr_cl                  false
% 7.70/1.48  --smt_preprocessing                     true
% 7.70/1.48  --smt_ac_axioms                         fast
% 7.70/1.48  --preprocessed_out                      false
% 7.70/1.48  --preprocessed_stats                    false
% 7.70/1.48  
% 7.70/1.48  ------ Abstraction refinement Options
% 7.70/1.48  
% 7.70/1.48  --abstr_ref                             []
% 7.70/1.48  --abstr_ref_prep                        false
% 7.70/1.48  --abstr_ref_until_sat                   false
% 7.70/1.48  --abstr_ref_sig_restrict                funpre
% 7.70/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.70/1.48  --abstr_ref_under                       []
% 7.70/1.48  
% 7.70/1.48  ------ SAT Options
% 7.70/1.48  
% 7.70/1.48  --sat_mode                              false
% 7.70/1.48  --sat_fm_restart_options                ""
% 7.70/1.48  --sat_gr_def                            false
% 7.70/1.48  --sat_epr_types                         true
% 7.70/1.48  --sat_non_cyclic_types                  false
% 7.70/1.48  --sat_finite_models                     false
% 7.70/1.48  --sat_fm_lemmas                         false
% 7.70/1.48  --sat_fm_prep                           false
% 7.70/1.48  --sat_fm_uc_incr                        true
% 7.70/1.48  --sat_out_model                         small
% 7.70/1.48  --sat_out_clauses                       false
% 7.70/1.48  
% 7.70/1.48  ------ QBF Options
% 7.70/1.48  
% 7.70/1.48  --qbf_mode                              false
% 7.70/1.48  --qbf_elim_univ                         false
% 7.70/1.48  --qbf_dom_inst                          none
% 7.70/1.48  --qbf_dom_pre_inst                      false
% 7.70/1.48  --qbf_sk_in                             false
% 7.70/1.48  --qbf_pred_elim                         true
% 7.70/1.48  --qbf_split                             512
% 7.70/1.48  
% 7.70/1.48  ------ BMC1 Options
% 7.70/1.48  
% 7.70/1.48  --bmc1_incremental                      false
% 7.70/1.48  --bmc1_axioms                           reachable_all
% 7.70/1.48  --bmc1_min_bound                        0
% 7.70/1.48  --bmc1_max_bound                        -1
% 7.70/1.48  --bmc1_max_bound_default                -1
% 7.70/1.48  --bmc1_symbol_reachability              true
% 7.70/1.48  --bmc1_property_lemmas                  false
% 7.70/1.48  --bmc1_k_induction                      false
% 7.70/1.48  --bmc1_non_equiv_states                 false
% 7.70/1.48  --bmc1_deadlock                         false
% 7.70/1.48  --bmc1_ucm                              false
% 7.70/1.48  --bmc1_add_unsat_core                   none
% 7.70/1.48  --bmc1_unsat_core_children              false
% 7.70/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.70/1.48  --bmc1_out_stat                         full
% 7.70/1.48  --bmc1_ground_init                      false
% 7.70/1.48  --bmc1_pre_inst_next_state              false
% 7.70/1.48  --bmc1_pre_inst_state                   false
% 7.70/1.48  --bmc1_pre_inst_reach_state             false
% 7.70/1.48  --bmc1_out_unsat_core                   false
% 7.70/1.48  --bmc1_aig_witness_out                  false
% 7.70/1.48  --bmc1_verbose                          false
% 7.70/1.48  --bmc1_dump_clauses_tptp                false
% 7.70/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.70/1.48  --bmc1_dump_file                        -
% 7.70/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.70/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.70/1.48  --bmc1_ucm_extend_mode                  1
% 7.70/1.48  --bmc1_ucm_init_mode                    2
% 7.70/1.48  --bmc1_ucm_cone_mode                    none
% 7.70/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.70/1.48  --bmc1_ucm_relax_model                  4
% 7.70/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.70/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.70/1.48  --bmc1_ucm_layered_model                none
% 7.70/1.48  --bmc1_ucm_max_lemma_size               10
% 7.70/1.48  
% 7.70/1.48  ------ AIG Options
% 7.70/1.48  
% 7.70/1.48  --aig_mode                              false
% 7.70/1.48  
% 7.70/1.48  ------ Instantiation Options
% 7.70/1.48  
% 7.70/1.48  --instantiation_flag                    true
% 7.70/1.48  --inst_sos_flag                         false
% 7.70/1.48  --inst_sos_phase                        true
% 7.70/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.70/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.70/1.48  --inst_lit_sel_side                     none
% 7.70/1.48  --inst_solver_per_active                1400
% 7.70/1.48  --inst_solver_calls_frac                1.
% 7.70/1.48  --inst_passive_queue_type               priority_queues
% 7.70/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.70/1.48  --inst_passive_queues_freq              [25;2]
% 7.70/1.48  --inst_dismatching                      true
% 7.70/1.48  --inst_eager_unprocessed_to_passive     true
% 7.70/1.48  --inst_prop_sim_given                   true
% 7.70/1.48  --inst_prop_sim_new                     false
% 7.70/1.48  --inst_subs_new                         false
% 7.70/1.48  --inst_eq_res_simp                      false
% 7.70/1.48  --inst_subs_given                       false
% 7.70/1.48  --inst_orphan_elimination               true
% 7.70/1.48  --inst_learning_loop_flag               true
% 7.70/1.48  --inst_learning_start                   3000
% 7.70/1.48  --inst_learning_factor                  2
% 7.70/1.48  --inst_start_prop_sim_after_learn       3
% 7.70/1.48  --inst_sel_renew                        solver
% 7.70/1.48  --inst_lit_activity_flag                true
% 7.70/1.48  --inst_restr_to_given                   false
% 7.70/1.48  --inst_activity_threshold               500
% 7.70/1.48  --inst_out_proof                        true
% 7.70/1.48  
% 7.70/1.48  ------ Resolution Options
% 7.70/1.48  
% 7.70/1.48  --resolution_flag                       false
% 7.70/1.48  --res_lit_sel                           adaptive
% 7.70/1.48  --res_lit_sel_side                      none
% 7.70/1.48  --res_ordering                          kbo
% 7.70/1.48  --res_to_prop_solver                    active
% 7.70/1.48  --res_prop_simpl_new                    false
% 7.70/1.48  --res_prop_simpl_given                  true
% 7.70/1.48  --res_passive_queue_type                priority_queues
% 7.70/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.70/1.48  --res_passive_queues_freq               [15;5]
% 7.70/1.48  --res_forward_subs                      full
% 7.70/1.48  --res_backward_subs                     full
% 7.70/1.48  --res_forward_subs_resolution           true
% 7.70/1.48  --res_backward_subs_resolution          true
% 7.70/1.48  --res_orphan_elimination                true
% 7.70/1.48  --res_time_limit                        2.
% 7.70/1.48  --res_out_proof                         true
% 7.70/1.48  
% 7.70/1.48  ------ Superposition Options
% 7.70/1.48  
% 7.70/1.48  --superposition_flag                    true
% 7.70/1.48  --sup_passive_queue_type                priority_queues
% 7.70/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.70/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.70/1.48  --demod_completeness_check              fast
% 7.70/1.48  --demod_use_ground                      true
% 7.70/1.48  --sup_to_prop_solver                    passive
% 7.70/1.48  --sup_prop_simpl_new                    true
% 7.70/1.48  --sup_prop_simpl_given                  true
% 7.70/1.48  --sup_fun_splitting                     false
% 7.70/1.48  --sup_smt_interval                      50000
% 7.70/1.48  
% 7.70/1.48  ------ Superposition Simplification Setup
% 7.70/1.48  
% 7.70/1.48  --sup_indices_passive                   []
% 7.70/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.70/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.70/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.70/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.70/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.70/1.48  --sup_full_bw                           [BwDemod]
% 7.70/1.48  --sup_immed_triv                        [TrivRules]
% 7.70/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.70/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.70/1.48  --sup_immed_bw_main                     []
% 7.70/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.70/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.70/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.70/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.70/1.48  
% 7.70/1.48  ------ Combination Options
% 7.70/1.48  
% 7.70/1.48  --comb_res_mult                         3
% 7.70/1.48  --comb_sup_mult                         2
% 7.70/1.48  --comb_inst_mult                        10
% 7.70/1.48  
% 7.70/1.48  ------ Debug Options
% 7.70/1.48  
% 7.70/1.48  --dbg_backtrace                         false
% 7.70/1.48  --dbg_dump_prop_clauses                 false
% 7.70/1.48  --dbg_dump_prop_clauses_file            -
% 7.70/1.48  --dbg_out_stat                          false
% 7.70/1.48  
% 7.70/1.48  
% 7.70/1.48  
% 7.70/1.48  
% 7.70/1.48  ------ Proving...
% 7.70/1.48  
% 7.70/1.48  
% 7.70/1.48  % SZS status Theorem for theBenchmark.p
% 7.70/1.48  
% 7.70/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.70/1.48  
% 7.70/1.48  fof(f1,axiom,(
% 7.70/1.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f41,plain,(
% 7.70/1.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.70/1.48    inference(nnf_transformation,[],[f1])).
% 7.70/1.48  
% 7.70/1.48  fof(f42,plain,(
% 7.70/1.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.70/1.48    inference(rectify,[],[f41])).
% 7.70/1.48  
% 7.70/1.48  fof(f43,plain,(
% 7.70/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.70/1.48    introduced(choice_axiom,[])).
% 7.70/1.48  
% 7.70/1.48  fof(f44,plain,(
% 7.70/1.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.70/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 7.70/1.48  
% 7.70/1.48  fof(f58,plain,(
% 7.70/1.48    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.70/1.48    inference(cnf_transformation,[],[f44])).
% 7.70/1.48  
% 7.70/1.48  fof(f21,conjecture,(
% 7.70/1.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f22,negated_conjecture,(
% 7.70/1.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 7.70/1.48    inference(negated_conjecture,[],[f21])).
% 7.70/1.48  
% 7.70/1.48  fof(f39,plain,(
% 7.70/1.48    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.70/1.48    inference(ennf_transformation,[],[f22])).
% 7.70/1.48  
% 7.70/1.48  fof(f40,plain,(
% 7.70/1.48    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.70/1.48    inference(flattening,[],[f39])).
% 7.70/1.48  
% 7.70/1.48  fof(f55,plain,(
% 7.70/1.48    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,sK6)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) )),
% 7.70/1.48    introduced(choice_axiom,[])).
% 7.70/1.48  
% 7.70/1.48  fof(f54,plain,(
% 7.70/1.48    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,sK5,X2)) | ~m1_subset_1(X3,sK5)) & k1_xboole_0 != k1_relset_1(X0,sK5,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK5)))) & ~v1_xboole_0(sK5))) )),
% 7.70/1.48    introduced(choice_axiom,[])).
% 7.70/1.48  
% 7.70/1.48  fof(f53,plain,(
% 7.70/1.48    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK4,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK4,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK4))),
% 7.70/1.48    introduced(choice_axiom,[])).
% 7.70/1.48  
% 7.70/1.48  fof(f56,plain,(
% 7.70/1.48    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK4,sK5,sK6)) | ~m1_subset_1(X3,sK5)) & k1_xboole_0 != k1_relset_1(sK4,sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)),
% 7.70/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f55,f54,f53])).
% 7.70/1.48  
% 7.70/1.48  fof(f88,plain,(
% 7.70/1.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 7.70/1.48    inference(cnf_transformation,[],[f56])).
% 7.70/1.48  
% 7.70/1.48  fof(f8,axiom,(
% 7.70/1.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f26,plain,(
% 7.70/1.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.70/1.48    inference(ennf_transformation,[],[f8])).
% 7.70/1.48  
% 7.70/1.48  fof(f27,plain,(
% 7.70/1.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.70/1.48    inference(flattening,[],[f26])).
% 7.70/1.48  
% 7.70/1.48  fof(f70,plain,(
% 7.70/1.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.70/1.48    inference(cnf_transformation,[],[f27])).
% 7.70/1.48  
% 7.70/1.48  fof(f6,axiom,(
% 7.70/1.48    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f68,plain,(
% 7.70/1.48    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.70/1.48    inference(cnf_transformation,[],[f6])).
% 7.70/1.48  
% 7.70/1.48  fof(f4,axiom,(
% 7.70/1.48    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f45,plain,(
% 7.70/1.48    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 7.70/1.48    inference(nnf_transformation,[],[f4])).
% 7.70/1.48  
% 7.70/1.48  fof(f46,plain,(
% 7.70/1.48    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 7.70/1.48    inference(rectify,[],[f45])).
% 7.70/1.48  
% 7.70/1.48  fof(f49,plain,(
% 7.70/1.48    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 7.70/1.48    introduced(choice_axiom,[])).
% 7.70/1.48  
% 7.70/1.48  fof(f48,plain,(
% 7.70/1.48    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 7.70/1.48    introduced(choice_axiom,[])).
% 7.70/1.48  
% 7.70/1.48  fof(f47,plain,(
% 7.70/1.48    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 7.70/1.48    introduced(choice_axiom,[])).
% 7.70/1.48  
% 7.70/1.48  fof(f50,plain,(
% 7.70/1.48    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 7.70/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f49,f48,f47])).
% 7.70/1.48  
% 7.70/1.48  fof(f63,plain,(
% 7.70/1.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 7.70/1.48    inference(cnf_transformation,[],[f50])).
% 7.70/1.48  
% 7.70/1.48  fof(f91,plain,(
% 7.70/1.48    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 7.70/1.48    inference(equality_resolution,[],[f63])).
% 7.70/1.48  
% 7.70/1.48  fof(f5,axiom,(
% 7.70/1.48    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f67,plain,(
% 7.70/1.48    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 7.70/1.48    inference(cnf_transformation,[],[f5])).
% 7.70/1.48  
% 7.70/1.48  fof(f9,axiom,(
% 7.70/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f51,plain,(
% 7.70/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.70/1.48    inference(nnf_transformation,[],[f9])).
% 7.70/1.48  
% 7.70/1.48  fof(f71,plain,(
% 7.70/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.70/1.48    inference(cnf_transformation,[],[f51])).
% 7.70/1.48  
% 7.70/1.48  fof(f19,axiom,(
% 7.70/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f37,plain,(
% 7.70/1.48    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.70/1.48    inference(ennf_transformation,[],[f19])).
% 7.70/1.48  
% 7.70/1.48  fof(f83,plain,(
% 7.70/1.48    ( ! [X2,X0,X1] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.70/1.48    inference(cnf_transformation,[],[f37])).
% 7.70/1.48  
% 7.70/1.48  fof(f16,axiom,(
% 7.70/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f34,plain,(
% 7.70/1.48    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.70/1.48    inference(ennf_transformation,[],[f16])).
% 7.70/1.48  
% 7.70/1.48  fof(f80,plain,(
% 7.70/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.70/1.48    inference(cnf_transformation,[],[f34])).
% 7.70/1.48  
% 7.70/1.48  fof(f10,axiom,(
% 7.70/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f28,plain,(
% 7.70/1.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.70/1.48    inference(ennf_transformation,[],[f10])).
% 7.70/1.48  
% 7.70/1.48  fof(f73,plain,(
% 7.70/1.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.70/1.48    inference(cnf_transformation,[],[f28])).
% 7.70/1.48  
% 7.70/1.48  fof(f72,plain,(
% 7.70/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.70/1.48    inference(cnf_transformation,[],[f51])).
% 7.70/1.48  
% 7.70/1.48  fof(f13,axiom,(
% 7.70/1.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f77,plain,(
% 7.70/1.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.70/1.48    inference(cnf_transformation,[],[f13])).
% 7.70/1.48  
% 7.70/1.48  fof(f14,axiom,(
% 7.70/1.48    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f31,plain,(
% 7.70/1.48    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 7.70/1.48    inference(ennf_transformation,[],[f14])).
% 7.70/1.48  
% 7.70/1.48  fof(f32,plain,(
% 7.70/1.48    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 7.70/1.48    inference(flattening,[],[f31])).
% 7.70/1.48  
% 7.70/1.48  fof(f78,plain,(
% 7.70/1.48    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 7.70/1.48    inference(cnf_transformation,[],[f32])).
% 7.70/1.48  
% 7.70/1.48  fof(f57,plain,(
% 7.70/1.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.70/1.48    inference(cnf_transformation,[],[f44])).
% 7.70/1.48  
% 7.70/1.48  fof(f18,axiom,(
% 7.70/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f36,plain,(
% 7.70/1.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.70/1.48    inference(ennf_transformation,[],[f18])).
% 7.70/1.48  
% 7.70/1.48  fof(f82,plain,(
% 7.70/1.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.70/1.48    inference(cnf_transformation,[],[f36])).
% 7.70/1.48  
% 7.70/1.48  fof(f20,axiom,(
% 7.70/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f38,plain,(
% 7.70/1.48    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.70/1.48    inference(ennf_transformation,[],[f20])).
% 7.70/1.48  
% 7.70/1.48  fof(f85,plain,(
% 7.70/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.70/1.48    inference(cnf_transformation,[],[f38])).
% 7.70/1.48  
% 7.70/1.48  fof(f17,axiom,(
% 7.70/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f35,plain,(
% 7.70/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.70/1.48    inference(ennf_transformation,[],[f17])).
% 7.70/1.48  
% 7.70/1.48  fof(f81,plain,(
% 7.70/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.70/1.48    inference(cnf_transformation,[],[f35])).
% 7.70/1.48  
% 7.70/1.48  fof(f12,axiom,(
% 7.70/1.48    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f30,plain,(
% 7.70/1.48    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 7.70/1.48    inference(ennf_transformation,[],[f12])).
% 7.70/1.48  
% 7.70/1.48  fof(f76,plain,(
% 7.70/1.48    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.70/1.48    inference(cnf_transformation,[],[f30])).
% 7.70/1.48  
% 7.70/1.48  fof(f84,plain,(
% 7.70/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.70/1.48    inference(cnf_transformation,[],[f38])).
% 7.70/1.48  
% 7.70/1.48  fof(f15,axiom,(
% 7.70/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f23,plain,(
% 7.70/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.70/1.48    inference(pure_predicate_removal,[],[f15])).
% 7.70/1.48  
% 7.70/1.48  fof(f33,plain,(
% 7.70/1.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.70/1.48    inference(ennf_transformation,[],[f23])).
% 7.70/1.48  
% 7.70/1.48  fof(f79,plain,(
% 7.70/1.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.70/1.48    inference(cnf_transformation,[],[f33])).
% 7.70/1.48  
% 7.70/1.48  fof(f11,axiom,(
% 7.70/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f29,plain,(
% 7.70/1.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.70/1.48    inference(ennf_transformation,[],[f11])).
% 7.70/1.48  
% 7.70/1.48  fof(f52,plain,(
% 7.70/1.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.70/1.48    inference(nnf_transformation,[],[f29])).
% 7.70/1.48  
% 7.70/1.48  fof(f74,plain,(
% 7.70/1.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.70/1.48    inference(cnf_transformation,[],[f52])).
% 7.70/1.48  
% 7.70/1.48  fof(f7,axiom,(
% 7.70/1.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f25,plain,(
% 7.70/1.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.70/1.48    inference(ennf_transformation,[],[f7])).
% 7.70/1.48  
% 7.70/1.48  fof(f69,plain,(
% 7.70/1.48    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.70/1.48    inference(cnf_transformation,[],[f25])).
% 7.70/1.48  
% 7.70/1.48  fof(f90,plain,(
% 7.70/1.48    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK4,sK5,sK6)) | ~m1_subset_1(X3,sK5)) )),
% 7.70/1.48    inference(cnf_transformation,[],[f56])).
% 7.70/1.48  
% 7.70/1.48  fof(f2,axiom,(
% 7.70/1.48    v1_xboole_0(k1_xboole_0)),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f59,plain,(
% 7.70/1.48    v1_xboole_0(k1_xboole_0)),
% 7.70/1.48    inference(cnf_transformation,[],[f2])).
% 7.70/1.48  
% 7.70/1.48  fof(f3,axiom,(
% 7.70/1.48    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 7.70/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.48  
% 7.70/1.48  fof(f24,plain,(
% 7.70/1.48    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 7.70/1.48    inference(ennf_transformation,[],[f3])).
% 7.70/1.48  
% 7.70/1.48  fof(f60,plain,(
% 7.70/1.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 7.70/1.48    inference(cnf_transformation,[],[f24])).
% 7.70/1.48  
% 7.70/1.48  fof(f89,plain,(
% 7.70/1.48    k1_xboole_0 != k1_relset_1(sK4,sK5,sK6)),
% 7.70/1.48    inference(cnf_transformation,[],[f56])).
% 7.70/1.48  
% 7.70/1.48  cnf(c_0,plain,
% 7.70/1.48      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.70/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1537,plain,
% 7.70/1.48      ( r2_hidden(sK0(X0),X0) = iProver_top
% 7.70/1.48      | v1_xboole_0(X0) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_31,negated_conjecture,
% 7.70/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 7.70/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1512,plain,
% 7.70/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_13,plain,
% 7.70/1.48      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.70/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1525,plain,
% 7.70/1.48      ( m1_subset_1(X0,X1) != iProver_top
% 7.70/1.48      | r2_hidden(X0,X1) = iProver_top
% 7.70/1.48      | v1_xboole_0(X1) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3275,plain,
% 7.70/1.48      ( r2_hidden(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top
% 7.70/1.48      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_1512,c_1525]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_36,plain,
% 7.70/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1788,plain,
% 7.70/1.48      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 7.70/1.48      | r2_hidden(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 7.70/1.48      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_13]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1789,plain,
% 7.70/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 7.70/1.48      | r2_hidden(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top
% 7.70/1.48      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_1788]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_11,plain,
% 7.70/1.48      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 7.70/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2419,plain,
% 7.70/1.48      ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2420,plain,
% 7.70/1.48      ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_2419]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3595,plain,
% 7.70/1.48      ( r2_hidden(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 7.70/1.48      inference(global_propositional_subsumption,
% 7.70/1.48                [status(thm)],
% 7.70/1.48                [c_3275,c_36,c_1789,c_2420]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_7,plain,
% 7.70/1.48      ( ~ r2_hidden(X0,X1)
% 7.70/1.48      | ~ r2_hidden(X2,X0)
% 7.70/1.48      | r2_hidden(X2,k3_tarski(X1)) ),
% 7.70/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1530,plain,
% 7.70/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.70/1.48      | r2_hidden(X2,X0) != iProver_top
% 7.70/1.48      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3600,plain,
% 7.70/1.48      ( r2_hidden(X0,k3_tarski(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))) = iProver_top
% 7.70/1.48      | r2_hidden(X0,sK6) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_3595,c_1530]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_10,plain,
% 7.70/1.48      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 7.70/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3606,plain,
% 7.70/1.48      ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) = iProver_top
% 7.70/1.48      | r2_hidden(X0,sK6) != iProver_top ),
% 7.70/1.48      inference(demodulation,[status(thm)],[c_3600,c_10]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3690,plain,
% 7.70/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.70/1.48      | r2_hidden(X0,k3_tarski(k2_zfmisc_1(sK4,sK5))) = iProver_top
% 7.70/1.48      | r2_hidden(X1,sK6) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_3606,c_1530]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3975,plain,
% 7.70/1.48      ( r2_hidden(X0,k3_tarski(k2_zfmisc_1(sK4,sK5))) = iProver_top
% 7.70/1.48      | r2_hidden(X0,sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_3606,c_3690]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_6666,plain,
% 7.70/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.70/1.48      | r2_hidden(X0,k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))) = iProver_top
% 7.70/1.48      | r2_hidden(X1,sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_3975,c_1530]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_8382,plain,
% 7.70/1.48      ( r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(sK6,k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))) = iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_3595,c_6666]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_8792,plain,
% 7.70/1.48      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5))))) = iProver_top
% 7.70/1.48      | r2_hidden(X0,sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_8382,c_1530]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_9516,plain,
% 7.70/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.70/1.48      | r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))))) = iProver_top
% 7.70/1.48      | r2_hidden(X1,sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_8792,c_1530]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_11097,plain,
% 7.70/1.48      ( r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(sK6,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))))) = iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_3595,c_9516]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_11404,plain,
% 7.70/1.48      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5))))))) = iProver_top
% 7.70/1.48      | r2_hidden(X0,sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_11097,c_1530]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_12039,plain,
% 7.70/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.70/1.48      | r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))))))) = iProver_top
% 7.70/1.48      | r2_hidden(X1,sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_11404,c_1530]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_12710,plain,
% 7.70/1.48      ( r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(sK6,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))))))) = iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_3595,c_12039]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_14260,plain,
% 7.70/1.48      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5))))))))) = iProver_top
% 7.70/1.48      | r2_hidden(X0,sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_12710,c_1530]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_14612,plain,
% 7.70/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.70/1.48      | r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))))))))) = iProver_top
% 7.70/1.48      | r2_hidden(X1,sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_14260,c_1530]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_15796,plain,
% 7.70/1.48      ( r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(sK6,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5)))))))))) = iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_3595,c_14612]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_16125,plain,
% 7.70/1.48      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(sK4,sK5))))))))))) = iProver_top
% 7.70/1.48      | r2_hidden(X0,sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k2_zfmisc_1(sK4,sK5),sK6) != iProver_top
% 7.70/1.48      | r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),sK6) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_15796,c_1530]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_15,plain,
% 7.70/1.48      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.70/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1759,plain,
% 7.70/1.48      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5))
% 7.70/1.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_15]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1760,plain,
% 7.70/1.48      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) = iProver_top
% 7.70/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_1759]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_26,plain,
% 7.70/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.48      | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
% 7.70/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1814,plain,
% 7.70/1.48      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 7.70/1.48      | k3_relset_1(sK4,sK5,sK6) = k4_relat_1(sK6) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_26]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_23,plain,
% 7.70/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.48      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.70/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1817,plain,
% 7.70/1.48      ( m1_subset_1(k3_relset_1(sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 7.70/1.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_23]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1818,plain,
% 7.70/1.48      ( m1_subset_1(k3_relset_1(sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top
% 7.70/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_1817]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1877,plain,
% 7.70/1.48      ( r1_tarski(k3_relset_1(sK4,sK5,sK6),k2_zfmisc_1(sK5,sK4))
% 7.70/1.48      | ~ m1_subset_1(k3_relset_1(sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_15]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1878,plain,
% 7.70/1.48      ( r1_tarski(k3_relset_1(sK4,sK5,sK6),k2_zfmisc_1(sK5,sK4)) = iProver_top
% 7.70/1.48      | m1_subset_1(k3_relset_1(sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_1877]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_16,plain,
% 7.70/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.70/1.48      | ~ v1_relat_1(X1)
% 7.70/1.48      | v1_relat_1(X0) ),
% 7.70/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_14,plain,
% 7.70/1.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.70/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_261,plain,
% 7.70/1.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.70/1.48      inference(prop_impl,[status(thm)],[c_14]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_318,plain,
% 7.70/1.48      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.70/1.48      inference(bin_hyper_res,[status(thm)],[c_16,c_261]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1839,plain,
% 7.70/1.48      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.70/1.48      | v1_relat_1(X0)
% 7.70/1.48      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_318]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2351,plain,
% 7.70/1.48      ( ~ r1_tarski(sK6,k2_zfmisc_1(sK4,sK5))
% 7.70/1.48      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
% 7.70/1.48      | v1_relat_1(sK6) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_1839]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2352,plain,
% 7.70/1.48      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) != iProver_top
% 7.70/1.48      | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 7.70/1.48      | v1_relat_1(sK6) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_2351]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_20,plain,
% 7.70/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.70/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2382,plain,
% 7.70/1.48      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_20]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2383,plain,
% 7.70/1.48      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_2382]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2585,plain,
% 7.70/1.48      ( v1_relat_1(k2_zfmisc_1(sK5,sK4)) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_20]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2586,plain,
% 7.70/1.48      ( v1_relat_1(k2_zfmisc_1(sK5,sK4)) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_2585]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_21,plain,
% 7.70/1.48      ( ~ v1_relat_1(X0)
% 7.70/1.48      | v1_xboole_0(X0)
% 7.70/1.48      | ~ v1_xboole_0(k1_relat_1(X0)) ),
% 7.70/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2626,plain,
% 7.70/1.48      ( ~ v1_relat_1(sK6)
% 7.70/1.48      | ~ v1_xboole_0(k1_relat_1(sK6))
% 7.70/1.48      | v1_xboole_0(sK6) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_21]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2627,plain,
% 7.70/1.48      ( v1_relat_1(sK6) != iProver_top
% 7.70/1.48      | v1_xboole_0(k1_relat_1(sK6)) != iProver_top
% 7.70/1.48      | v1_xboole_0(sK6) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_2626]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_821,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2114,plain,
% 7.70/1.48      ( X0 != X1
% 7.70/1.48      | X0 = k3_relset_1(sK4,sK5,sK6)
% 7.70/1.48      | k3_relset_1(sK4,sK5,sK6) != X1 ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_821]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2959,plain,
% 7.70/1.48      ( X0 = k3_relset_1(sK4,sK5,sK6)
% 7.70/1.48      | X0 != k4_relat_1(sK6)
% 7.70/1.48      | k3_relset_1(sK4,sK5,sK6) != k4_relat_1(sK6) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_2114]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3589,plain,
% 7.70/1.48      ( k3_relset_1(sK4,sK5,sK6) != k4_relat_1(sK6)
% 7.70/1.48      | k4_relat_1(sK6) = k3_relset_1(sK4,sK5,sK6)
% 7.70/1.48      | k4_relat_1(sK6) != k4_relat_1(sK6) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_2959]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_820,plain,( X0 = X0 ),theory(equality) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3590,plain,
% 7.70/1.48      ( k4_relat_1(sK6) = k4_relat_1(sK6) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_820]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1,plain,
% 7.70/1.48      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.70/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3639,plain,
% 7.70/1.48      ( ~ r2_hidden(X0,sK6) | ~ v1_xboole_0(sK6) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3640,plain,
% 7.70/1.48      ( r2_hidden(X0,sK6) != iProver_top
% 7.70/1.48      | v1_xboole_0(sK6) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_3639]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_827,plain,
% 7.70/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.70/1.48      theory(equality) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1975,plain,
% 7.70/1.48      ( r1_tarski(X0,k2_zfmisc_1(sK5,sK4))
% 7.70/1.48      | ~ r1_tarski(k3_relset_1(sK4,sK5,sK6),k2_zfmisc_1(sK5,sK4))
% 7.70/1.48      | X0 != k3_relset_1(sK4,sK5,sK6) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_827]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3718,plain,
% 7.70/1.48      ( ~ r1_tarski(k3_relset_1(sK4,sK5,sK6),k2_zfmisc_1(sK5,sK4))
% 7.70/1.48      | r1_tarski(k4_relat_1(sK6),k2_zfmisc_1(sK5,sK4))
% 7.70/1.48      | k4_relat_1(sK6) != k3_relset_1(sK4,sK5,sK6) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_1975]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3724,plain,
% 7.70/1.48      ( k4_relat_1(sK6) != k3_relset_1(sK4,sK5,sK6)
% 7.70/1.48      | r1_tarski(k3_relset_1(sK4,sK5,sK6),k2_zfmisc_1(sK5,sK4)) != iProver_top
% 7.70/1.48      | r1_tarski(k4_relat_1(sK6),k2_zfmisc_1(sK5,sK4)) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_3718]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1516,plain,
% 7.70/1.48      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
% 7.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2614,plain,
% 7.70/1.48      ( k3_relset_1(sK4,sK5,sK6) = k4_relat_1(sK6) ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_1512,c_1516]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1519,plain,
% 7.70/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.70/1.48      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_4020,plain,
% 7.70/1.48      ( m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top
% 7.70/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_2614,c_1519]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_4602,plain,
% 7.70/1.48      ( m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
% 7.70/1.48      inference(global_propositional_subsumption,
% 7.70/1.48                [status(thm)],
% 7.70/1.48                [c_4020,c_36]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_25,plain,
% 7.70/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.70/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1517,plain,
% 7.70/1.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_4613,plain,
% 7.70/1.48      ( k2_relset_1(sK5,sK4,k4_relat_1(sK6)) = k2_relat_1(k4_relat_1(sK6)) ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_4602,c_1517]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_27,plain,
% 7.70/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.48      | k2_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k1_relset_1(X1,X2,X0) ),
% 7.70/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1515,plain,
% 7.70/1.48      ( k2_relset_1(X0,X1,k3_relset_1(X1,X0,X2)) = k1_relset_1(X1,X0,X2)
% 7.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3138,plain,
% 7.70/1.48      ( k2_relset_1(sK5,sK4,k3_relset_1(sK4,sK5,sK6)) = k1_relset_1(sK4,sK5,sK6) ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_1512,c_1515]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3140,plain,
% 7.70/1.48      ( k2_relset_1(sK5,sK4,k4_relat_1(sK6)) = k1_relset_1(sK4,sK5,sK6) ),
% 7.70/1.48      inference(light_normalisation,[status(thm)],[c_3138,c_2614]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_24,plain,
% 7.70/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.70/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1518,plain,
% 7.70/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3153,plain,
% 7.70/1.48      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_1512,c_1518]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3685,plain,
% 7.70/1.48      ( k2_relset_1(sK5,sK4,k4_relat_1(sK6)) = k1_relat_1(sK6) ),
% 7.70/1.48      inference(light_normalisation,[status(thm)],[c_3140,c_3153]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_4618,plain,
% 7.70/1.48      ( k2_relat_1(k4_relat_1(sK6)) = k1_relat_1(sK6) ),
% 7.70/1.48      inference(light_normalisation,[status(thm)],[c_4613,c_3685]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_19,plain,
% 7.70/1.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0)) ),
% 7.70/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1522,plain,
% 7.70/1.48      ( v1_xboole_0(X0) != iProver_top
% 7.70/1.48      | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_4881,plain,
% 7.70/1.48      ( v1_xboole_0(k4_relat_1(sK6)) != iProver_top
% 7.70/1.48      | v1_xboole_0(k1_relat_1(sK6)) = iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_4618,c_1522]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_4612,plain,
% 7.70/1.48      ( k1_relset_1(sK5,sK4,k4_relat_1(sK6)) = k1_relat_1(k4_relat_1(sK6)) ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_4602,c_1518]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_28,plain,
% 7.70/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.48      | k1_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k2_relset_1(X1,X2,X0) ),
% 7.70/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1514,plain,
% 7.70/1.48      ( k1_relset_1(X0,X1,k3_relset_1(X1,X0,X2)) = k2_relset_1(X1,X0,X2)
% 7.70/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2510,plain,
% 7.70/1.48      ( k1_relset_1(sK5,sK4,k3_relset_1(sK4,sK5,sK6)) = k2_relset_1(sK4,sK5,sK6) ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_1512,c_1514]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2745,plain,
% 7.70/1.48      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_1512,c_1517]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2896,plain,
% 7.70/1.48      ( k1_relset_1(sK5,sK4,k4_relat_1(sK6)) = k2_relat_1(sK6) ),
% 7.70/1.48      inference(light_normalisation,[status(thm)],[c_2510,c_2614,c_2745]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_4621,plain,
% 7.70/1.48      ( k1_relat_1(k4_relat_1(sK6)) = k2_relat_1(sK6) ),
% 7.70/1.48      inference(light_normalisation,[status(thm)],[c_4612,c_2896]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1520,plain,
% 7.70/1.48      ( v1_relat_1(X0) != iProver_top
% 7.70/1.48      | v1_xboole_0(X0) = iProver_top
% 7.70/1.48      | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_4884,plain,
% 7.70/1.48      ( v1_relat_1(k4_relat_1(sK6)) != iProver_top
% 7.70/1.48      | v1_xboole_0(k4_relat_1(sK6)) = iProver_top
% 7.70/1.48      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_4621,c_1520]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_7462,plain,
% 7.70/1.48      ( ~ r1_tarski(k4_relat_1(sK6),k2_zfmisc_1(sK5,sK4))
% 7.70/1.48      | ~ v1_relat_1(k2_zfmisc_1(sK5,sK4))
% 7.70/1.48      | v1_relat_1(k4_relat_1(sK6)) ),
% 7.70/1.48      inference(instantiation,[status(thm)],[c_1839]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_7463,plain,
% 7.70/1.48      ( r1_tarski(k4_relat_1(sK6),k2_zfmisc_1(sK5,sK4)) != iProver_top
% 7.70/1.48      | v1_relat_1(k2_zfmisc_1(sK5,sK4)) != iProver_top
% 7.70/1.48      | v1_relat_1(k4_relat_1(sK6)) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_7462]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_4614,plain,
% 7.70/1.48      ( k3_relset_1(sK5,sK4,k4_relat_1(sK6)) = k4_relat_1(k4_relat_1(sK6)) ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_4602,c_1516]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_4962,plain,
% 7.70/1.48      ( m1_subset_1(k4_relat_1(k4_relat_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top
% 7.70/1.48      | m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_4614,c_1519]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_5610,plain,
% 7.70/1.48      ( m1_subset_1(k4_relat_1(k4_relat_1(sK6)),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 7.70/1.48      inference(global_propositional_subsumption,
% 7.70/1.48                [status(thm)],
% 7.70/1.48                [c_4962,c_36,c_4020]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_22,plain,
% 7.70/1.48      ( v5_relat_1(X0,X1)
% 7.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.70/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_18,plain,
% 7.70/1.48      ( ~ v5_relat_1(X0,X1)
% 7.70/1.48      | r1_tarski(k2_relat_1(X0),X1)
% 7.70/1.48      | ~ v1_relat_1(X0) ),
% 7.70/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_428,plain,
% 7.70/1.48      ( r1_tarski(k2_relat_1(X0),X1)
% 7.70/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.70/1.48      | ~ v1_relat_1(X0) ),
% 7.70/1.48      inference(resolution,[status(thm)],[c_22,c_18]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1508,plain,
% 7.70/1.48      ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 7.70/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 7.70/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_5617,plain,
% 7.70/1.48      ( r1_tarski(k2_relat_1(k4_relat_1(k4_relat_1(sK6))),sK5) = iProver_top
% 7.70/1.48      | v1_relat_1(k4_relat_1(k4_relat_1(sK6))) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_5610,c_1508]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_5621,plain,
% 7.70/1.48      ( k2_relset_1(sK4,sK5,k4_relat_1(k4_relat_1(sK6))) = k2_relat_1(k4_relat_1(k4_relat_1(sK6))) ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_5610,c_1517]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_4610,plain,
% 7.70/1.48      ( k2_relset_1(sK4,sK5,k3_relset_1(sK5,sK4,k4_relat_1(sK6))) = k1_relset_1(sK5,sK4,k4_relat_1(sK6)) ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_4602,c_1515]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_4627,plain,
% 7.70/1.48      ( k2_relset_1(sK4,sK5,k4_relat_1(k4_relat_1(sK6))) = k1_relset_1(sK5,sK4,k4_relat_1(sK6)) ),
% 7.70/1.48      inference(light_normalisation,[status(thm)],[c_4610,c_4614]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_4629,plain,
% 7.70/1.48      ( k2_relset_1(sK4,sK5,k4_relat_1(k4_relat_1(sK6))) = k2_relat_1(sK6) ),
% 7.70/1.48      inference(light_normalisation,[status(thm)],[c_4627,c_2896]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_5626,plain,
% 7.70/1.48      ( k2_relat_1(k4_relat_1(k4_relat_1(sK6))) = k2_relat_1(sK6) ),
% 7.70/1.48      inference(light_normalisation,[status(thm)],[c_5621,c_4629]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_5639,plain,
% 7.70/1.48      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
% 7.70/1.48      | v1_relat_1(k4_relat_1(k4_relat_1(sK6))) != iProver_top ),
% 7.70/1.48      inference(light_normalisation,[status(thm)],[c_5617,c_5626]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1865,plain,
% 7.70/1.48      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
% 7.70/1.48      | v1_relat_1(sK6) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_1512,c_1508]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_6858,plain,
% 7.70/1.48      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 7.70/1.48      inference(global_propositional_subsumption,
% 7.70/1.48                [status(thm)],
% 7.70/1.48                [c_5639,c_36,c_1760,c_1865,c_2352,c_2383]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1524,plain,
% 7.70/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.70/1.48      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3274,plain,
% 7.70/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.70/1.48      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.70/1.48      | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_1524,c_1525]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1527,plain,
% 7.70/1.48      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_16295,plain,
% 7.70/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.70/1.48      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.70/1.48      inference(forward_subsumption_resolution,
% 7.70/1.48                [status(thm)],
% 7.70/1.48                [c_3274,c_1527]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_16304,plain,
% 7.70/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.70/1.48      | r2_hidden(X2,X0) != iProver_top
% 7.70/1.48      | r2_hidden(X2,k3_tarski(k1_zfmisc_1(X1))) = iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_16295,c_1530]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_16321,plain,
% 7.70/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.70/1.48      | r2_hidden(X2,X0) != iProver_top
% 7.70/1.48      | r2_hidden(X2,X1) = iProver_top ),
% 7.70/1.48      inference(demodulation,[status(thm)],[c_16304,c_10]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_16460,plain,
% 7.70/1.48      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 7.70/1.48      | r2_hidden(X0,sK5) = iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_6858,c_16321]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_16518,plain,
% 7.70/1.48      ( r2_hidden(sK0(k2_relat_1(sK6)),sK5) = iProver_top
% 7.70/1.48      | v1_xboole_0(k2_relat_1(sK6)) = iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_1537,c_16460]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_12,plain,
% 7.70/1.48      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.70/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1526,plain,
% 7.70/1.48      ( m1_subset_1(X0,X1) = iProver_top
% 7.70/1.48      | r2_hidden(X0,X1) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_16593,plain,
% 7.70/1.48      ( m1_subset_1(sK0(k2_relat_1(sK6)),sK5) = iProver_top
% 7.70/1.48      | v1_xboole_0(k2_relat_1(sK6)) = iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_16518,c_1526]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_29,negated_conjecture,
% 7.70/1.48      ( ~ m1_subset_1(X0,sK5)
% 7.70/1.48      | ~ r2_hidden(X0,k2_relset_1(sK4,sK5,sK6)) ),
% 7.70/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1513,plain,
% 7.70/1.48      ( m1_subset_1(X0,sK5) != iProver_top
% 7.70/1.48      | r2_hidden(X0,k2_relset_1(sK4,sK5,sK6)) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1989,plain,
% 7.70/1.48      ( m1_subset_1(sK0(k2_relset_1(sK4,sK5,sK6)),sK5) != iProver_top
% 7.70/1.48      | v1_xboole_0(k2_relset_1(sK4,sK5,sK6)) = iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_1537,c_1513]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2882,plain,
% 7.70/1.48      ( m1_subset_1(sK0(k2_relat_1(sK6)),sK5) != iProver_top
% 7.70/1.48      | v1_xboole_0(k2_relat_1(sK6)) = iProver_top ),
% 7.70/1.48      inference(demodulation,[status(thm)],[c_2745,c_1989]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_16658,plain,
% 7.70/1.48      ( v1_xboole_0(k2_relat_1(sK6)) = iProver_top ),
% 7.70/1.48      inference(global_propositional_subsumption,
% 7.70/1.48                [status(thm)],
% 7.70/1.48                [c_16593,c_2882]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_16795,plain,
% 7.70/1.48      ( r2_hidden(X0,sK6) != iProver_top ),
% 7.70/1.48      inference(global_propositional_subsumption,
% 7.70/1.48                [status(thm)],
% 7.70/1.48                [c_16125,c_31,c_36,c_1760,c_1814,c_1818,c_1878,c_2352,
% 7.70/1.48                 c_2383,c_2586,c_2627,c_2882,c_3589,c_3590,c_3640,c_3724,
% 7.70/1.48                 c_4881,c_4884,c_7463,c_16593]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_16802,plain,
% 7.70/1.48      ( v1_xboole_0(sK6) = iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_1537,c_16795]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2,plain,
% 7.70/1.48      ( v1_xboole_0(k1_xboole_0) ),
% 7.70/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1535,plain,
% 7.70/1.48      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3,plain,
% 7.70/1.48      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 7.70/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_1534,plain,
% 7.70/1.48      ( X0 = X1
% 7.70/1.48      | v1_xboole_0(X1) != iProver_top
% 7.70/1.48      | v1_xboole_0(X0) != iProver_top ),
% 7.70/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_2596,plain,
% 7.70/1.48      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_1535,c_1534]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_16930,plain,
% 7.70/1.48      ( sK6 = k1_xboole_0 ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_16802,c_2596]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_18441,plain,
% 7.70/1.48      ( v1_xboole_0(k4_relat_1(k1_xboole_0)) != iProver_top
% 7.70/1.48      | v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top ),
% 7.70/1.48      inference(demodulation,[status(thm)],[c_16930,c_4881]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_16673,plain,
% 7.70/1.48      ( v1_relat_1(k4_relat_1(sK6)) != iProver_top
% 7.70/1.48      | v1_xboole_0(k4_relat_1(sK6)) = iProver_top ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_16658,c_4884]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_22329,plain,
% 7.70/1.48      ( v1_xboole_0(k4_relat_1(sK6)) = iProver_top ),
% 7.70/1.48      inference(global_propositional_subsumption,
% 7.70/1.48                [status(thm)],
% 7.70/1.48                [c_16673,c_31,c_36,c_1814,c_1818,c_1878,c_2586,c_2882,
% 7.70/1.48                 c_3589,c_3590,c_3724,c_4884,c_7463,c_16593]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_22333,plain,
% 7.70/1.48      ( v1_xboole_0(k4_relat_1(k1_xboole_0)) = iProver_top ),
% 7.70/1.48      inference(light_normalisation,[status(thm)],[c_22329,c_16930]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_22364,plain,
% 7.70/1.48      ( v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top ),
% 7.70/1.48      inference(global_propositional_subsumption,
% 7.70/1.48                [status(thm)],
% 7.70/1.48                [c_18441,c_22333]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_22377,plain,
% 7.70/1.48      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.70/1.48      inference(superposition,[status(thm)],[c_22364,c_2596]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_30,negated_conjecture,
% 7.70/1.48      ( k1_xboole_0 != k1_relset_1(sK4,sK5,sK6) ),
% 7.70/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_3495,plain,
% 7.70/1.48      ( k1_relat_1(sK6) != k1_xboole_0 ),
% 7.70/1.48      inference(demodulation,[status(thm)],[c_3153,c_30]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(c_18455,plain,
% 7.70/1.48      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 7.70/1.48      inference(demodulation,[status(thm)],[c_16930,c_3495]) ).
% 7.70/1.48  
% 7.70/1.48  cnf(contradiction,plain,
% 7.70/1.48      ( $false ),
% 7.70/1.48      inference(minisat,[status(thm)],[c_22377,c_18455]) ).
% 7.70/1.48  
% 7.70/1.48  
% 7.70/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.70/1.48  
% 7.70/1.48  ------                               Statistics
% 7.70/1.48  
% 7.70/1.48  ------ General
% 7.70/1.48  
% 7.70/1.48  abstr_ref_over_cycles:                  0
% 7.70/1.48  abstr_ref_under_cycles:                 0
% 7.70/1.48  gc_basic_clause_elim:                   0
% 7.70/1.48  forced_gc_time:                         0
% 7.70/1.48  parsing_time:                           0.01
% 7.70/1.48  unif_index_cands_time:                  0.
% 7.70/1.48  unif_index_add_time:                    0.
% 7.70/1.48  orderings_time:                         0.
% 7.70/1.48  out_proof_time:                         0.014
% 7.70/1.48  total_time:                             0.559
% 7.70/1.48  num_of_symbols:                         54
% 7.70/1.48  num_of_terms:                           21190
% 7.70/1.48  
% 7.70/1.48  ------ Preprocessing
% 7.70/1.48  
% 7.70/1.48  num_of_splits:                          0
% 7.70/1.48  num_of_split_atoms:                     0
% 7.70/1.48  num_of_reused_defs:                     0
% 7.70/1.48  num_eq_ax_congr_red:                    44
% 7.70/1.48  num_of_sem_filtered_clauses:            1
% 7.70/1.48  num_of_subtypes:                        0
% 7.70/1.48  monotx_restored_types:                  0
% 7.70/1.48  sat_num_of_epr_types:                   0
% 7.70/1.48  sat_num_of_non_cyclic_types:            0
% 7.70/1.48  sat_guarded_non_collapsed_types:        0
% 7.70/1.48  num_pure_diseq_elim:                    0
% 7.70/1.48  simp_replaced_by:                       0
% 7.70/1.48  res_preprocessed:                       155
% 7.70/1.48  prep_upred:                             0
% 7.70/1.48  prep_unflattend:                        8
% 7.70/1.48  smt_new_axioms:                         0
% 7.70/1.48  pred_elim_cands:                        5
% 7.70/1.48  pred_elim:                              1
% 7.70/1.48  pred_elim_cl:                           2
% 7.70/1.48  pred_elim_cycles:                       3
% 7.70/1.48  merged_defs:                            8
% 7.70/1.48  merged_defs_ncl:                        0
% 7.70/1.48  bin_hyper_res:                          9
% 7.70/1.48  prep_cycles:                            4
% 7.70/1.48  pred_elim_time:                         0.004
% 7.70/1.48  splitting_time:                         0.
% 7.70/1.48  sem_filter_time:                        0.
% 7.70/1.48  monotx_time:                            0.001
% 7.70/1.48  subtype_inf_time:                       0.
% 7.70/1.48  
% 7.70/1.48  ------ Problem properties
% 7.70/1.48  
% 7.70/1.48  clauses:                                32
% 7.70/1.48  conjectures:                            5
% 7.70/1.48  epr:                                    8
% 7.70/1.48  horn:                                   28
% 7.70/1.48  ground:                                 5
% 7.70/1.48  unary:                                  8
% 7.70/1.48  binary:                                 15
% 7.70/1.48  lits:                                   66
% 7.70/1.48  lits_eq:                                11
% 7.70/1.48  fd_pure:                                0
% 7.70/1.48  fd_pseudo:                              0
% 7.70/1.48  fd_cond:                                0
% 7.70/1.48  fd_pseudo_cond:                         4
% 7.70/1.48  ac_symbols:                             0
% 7.70/1.49  
% 7.70/1.49  ------ Propositional Solver
% 7.70/1.49  
% 7.70/1.49  prop_solver_calls:                      30
% 7.70/1.49  prop_fast_solver_calls:                 1293
% 7.70/1.49  smt_solver_calls:                       0
% 7.70/1.49  smt_fast_solver_calls:                  0
% 7.70/1.49  prop_num_of_clauses:                    8752
% 7.70/1.49  prop_preprocess_simplified:             16133
% 7.70/1.49  prop_fo_subsumed:                       17
% 7.70/1.49  prop_solver_time:                       0.
% 7.70/1.49  smt_solver_time:                        0.
% 7.70/1.49  smt_fast_solver_time:                   0.
% 7.70/1.49  prop_fast_solver_time:                  0.
% 7.70/1.49  prop_unsat_core_time:                   0.
% 7.70/1.49  
% 7.70/1.49  ------ QBF
% 7.70/1.49  
% 7.70/1.49  qbf_q_res:                              0
% 7.70/1.49  qbf_num_tautologies:                    0
% 7.70/1.49  qbf_prep_cycles:                        0
% 7.70/1.49  
% 7.70/1.49  ------ BMC1
% 7.70/1.49  
% 7.70/1.49  bmc1_current_bound:                     -1
% 7.70/1.49  bmc1_last_solved_bound:                 -1
% 7.70/1.49  bmc1_unsat_core_size:                   -1
% 7.70/1.49  bmc1_unsat_core_parents_size:           -1
% 7.70/1.49  bmc1_merge_next_fun:                    0
% 7.70/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.70/1.49  
% 7.70/1.49  ------ Instantiation
% 7.70/1.49  
% 7.70/1.49  inst_num_of_clauses:                    2396
% 7.70/1.49  inst_num_in_passive:                    512
% 7.70/1.49  inst_num_in_active:                     1011
% 7.70/1.49  inst_num_in_unprocessed:                873
% 7.70/1.49  inst_num_of_loops:                      1170
% 7.70/1.49  inst_num_of_learning_restarts:          0
% 7.70/1.49  inst_num_moves_active_passive:          156
% 7.70/1.49  inst_lit_activity:                      0
% 7.70/1.49  inst_lit_activity_moves:                0
% 7.70/1.49  inst_num_tautologies:                   0
% 7.70/1.49  inst_num_prop_implied:                  0
% 7.70/1.49  inst_num_existing_simplified:           0
% 7.70/1.49  inst_num_eq_res_simplified:             0
% 7.70/1.49  inst_num_child_elim:                    0
% 7.70/1.49  inst_num_of_dismatching_blockings:      1222
% 7.70/1.49  inst_num_of_non_proper_insts:           2186
% 7.70/1.49  inst_num_of_duplicates:                 0
% 7.70/1.49  inst_inst_num_from_inst_to_res:         0
% 7.70/1.49  inst_dismatching_checking_time:         0.
% 7.70/1.49  
% 7.70/1.49  ------ Resolution
% 7.70/1.49  
% 7.70/1.49  res_num_of_clauses:                     0
% 7.70/1.49  res_num_in_passive:                     0
% 7.70/1.49  res_num_in_active:                      0
% 7.70/1.49  res_num_of_loops:                       159
% 7.70/1.49  res_forward_subset_subsumed:            282
% 7.70/1.49  res_backward_subset_subsumed:           12
% 7.70/1.49  res_forward_subsumed:                   0
% 7.70/1.49  res_backward_subsumed:                  0
% 7.70/1.49  res_forward_subsumption_resolution:     0
% 7.70/1.49  res_backward_subsumption_resolution:    0
% 7.70/1.49  res_clause_to_clause_subsumption:       2842
% 7.70/1.49  res_orphan_elimination:                 0
% 7.70/1.49  res_tautology_del:                      181
% 7.70/1.49  res_num_eq_res_simplified:              0
% 7.70/1.49  res_num_sel_changes:                    0
% 7.70/1.49  res_moves_from_active_to_pass:          0
% 7.70/1.49  
% 7.70/1.49  ------ Superposition
% 7.70/1.49  
% 7.70/1.49  sup_time_total:                         0.
% 7.70/1.49  sup_time_generating:                    0.
% 7.70/1.49  sup_time_sim_full:                      0.
% 7.70/1.49  sup_time_sim_immed:                     0.
% 7.70/1.49  
% 7.70/1.49  sup_num_of_clauses:                     438
% 7.70/1.49  sup_num_in_active:                      107
% 7.70/1.49  sup_num_in_passive:                     331
% 7.70/1.49  sup_num_of_loops:                       233
% 7.70/1.49  sup_fw_superposition:                   358
% 7.70/1.49  sup_bw_superposition:                   530
% 7.70/1.49  sup_immediate_simplified:               366
% 7.70/1.49  sup_given_eliminated:                   8
% 7.70/1.49  comparisons_done:                       0
% 7.70/1.49  comparisons_avoided:                    15
% 7.70/1.49  
% 7.70/1.49  ------ Simplifications
% 7.70/1.49  
% 7.70/1.49  
% 7.70/1.49  sim_fw_subset_subsumed:                 92
% 7.70/1.49  sim_bw_subset_subsumed:                 61
% 7.70/1.49  sim_fw_subsumed:                        58
% 7.70/1.49  sim_bw_subsumed:                        70
% 7.70/1.49  sim_fw_subsumption_res:                 2
% 7.70/1.49  sim_bw_subsumption_res:                 0
% 7.70/1.49  sim_tautology_del:                      8
% 7.70/1.49  sim_eq_tautology_del:                   24
% 7.70/1.49  sim_eq_res_simp:                        0
% 7.70/1.49  sim_fw_demodulated:                     28
% 7.70/1.49  sim_bw_demodulated:                     135
% 7.70/1.49  sim_light_normalised:                   119
% 7.70/1.49  sim_joinable_taut:                      0
% 7.70/1.49  sim_joinable_simp:                      0
% 7.70/1.49  sim_ac_normalised:                      0
% 7.70/1.49  sim_smt_subsumption:                    0
% 7.70/1.49  
%------------------------------------------------------------------------------
