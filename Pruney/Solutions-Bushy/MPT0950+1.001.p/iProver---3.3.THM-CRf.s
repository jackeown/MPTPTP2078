%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0950+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:29 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :  198 (5583 expanded)
%              Number of clauses        :  123 (2078 expanded)
%              Number of leaves         :   21 (1036 expanded)
%              Depth                    :   39
%              Number of atoms          :  699 (19952 expanded)
%              Number of equality atoms :  339 (4946 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r1_tarski(X0,X1)
       => r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ( r1_tarski(X0,X1)
         => r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f46,plain,(
    ? [X0,X1] :
      ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ? [X0,X1] :
      ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f58,plain,
    ( ? [X0,X1] :
        ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
        & r1_tarski(X0,X1)
        & v3_ordinal1(X1) )
   => ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4)
      & r1_tarski(sK3,sK4)
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4)
    & r1_tarski(sK3,sK4)
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f58])).

fof(f88,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] :
              ~ ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
                & r2_hidden(X2,k3_relat_1(X1)) )
          & ~ r4_wellord1(X1,k2_wellord1(X1,X0))
          & v2_wellord1(X1)
          & r1_tarski(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
          & r2_hidden(X2,k3_relat_1(X1)) )
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
          & r2_hidden(X2,k3_relat_1(X1)) )
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
          & r2_hidden(X2,k3_relat_1(X1)) )
     => ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,sK2(X0,X1))),k2_wellord1(X1,X0))
        & r2_hidden(sK2(X0,X1),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,sK2(X0,X1))),k2_wellord1(X1,X0))
        & r2_hidden(sK2(X0,X1),k3_relat_1(X1)) )
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f56])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,sK2(X0,X1))),k2_wellord1(X1,X0))
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK0(X0,X1),sK1(X0,X1))
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( r1_tarski(sK0(X0,X1),sK1(X0,X1))
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK0(X0,X1),sK1(X0,X1))
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( r1_tarski(sK0(X0,X1),sK1(X0,X1))
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & r2_hidden(sK1(X0,X1),X0)
            & r2_hidden(sK0(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f51])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f96,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( r1_tarski(X1,X0)
         => v2_wellord1(k1_wellord2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_wellord1(k1_wellord2(X1))
          | ~ r1_tarski(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k1_wellord2(X1))
      | ~ r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => r1_ordinal1(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_relat_1(X1))
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_ordinal1(X1)
          | ~ m1_subset_1(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( k2_wellord2(X0) = X1
            <=> r4_wellord1(X0,k1_wellord2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_wellord2(X0) = X1
          <=> r4_wellord1(X0,k1_wellord2(X1)) )
          | ~ v3_ordinal1(X1) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_wellord2(X0) = X1
          <=> r4_wellord1(X0,k1_wellord2(X1)) )
          | ~ v3_ordinal1(X1) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_wellord2(X0) = X1
              | ~ r4_wellord1(X0,k1_wellord2(X1)) )
            & ( r4_wellord1(X0,k1_wellord2(X1))
              | k2_wellord2(X0) != X1 ) )
          | ~ v3_ordinal1(X1) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_wellord2(X0) = X1
      | ~ r4_wellord1(X0,k1_wellord2(X1))
      | ~ v3_ordinal1(X1)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1071,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1074,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1681,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3) ),
    inference(superposition,[status(thm)],[c_1071,c_1074])).

cnf(c_23,plain,
    ( r4_wellord1(X0,k2_wellord1(X0,X1))
    | r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,sK2(X1,X0))),k2_wellord1(X0,X1))
    | ~ r1_tarski(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1076,plain,
    ( r4_wellord1(X0,k2_wellord1(X0,X1)) = iProver_top
    | r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,sK2(X1,X0))),k2_wellord1(X0,X1)) = iProver_top
    | r1_tarski(X1,k3_relat_1(X0)) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3060,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4)))),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) = iProver_top
    | r1_tarski(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1681,c_1076])).

cnf(c_3061,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4)))),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_tarski(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3060,c_1681])).

cnf(c_9,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_13,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_288,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_13])).

cnf(c_3062,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4)))),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_tarski(sK3,sK4) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3061,c_288])).

cnf(c_29,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_30,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_31,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_26,plain,
    ( ~ r1_tarski(X0,X1)
    | v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_33,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v2_wellord1(k1_wellord2(X0)) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_35,plain,
    ( r1_tarski(sK4,sK4) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_17,plain,
    ( r1_ordinal1(X0,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_58,plain,
    ( r1_ordinal1(X0,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_60,plain,
    ( r1_ordinal1(sK4,sK4) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_61,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_ordinal1(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_63,plain,
    ( r1_tarski(sK4,sK4) = iProver_top
    | r1_ordinal1(sK4,sK4) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_70,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_72,plain,
    ( v1_relat_1(k1_wellord2(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_11220,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4)))),k1_wellord2(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3062,c_30,c_31,c_35,c_60,c_63,c_72])).

cnf(c_11221,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4)))),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_11220])).

cnf(c_22,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1077,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_11227,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))))) = iProver_top
    | v1_relat_1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))))) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11221,c_1077])).

cnf(c_1728,plain,
    ( v1_relat_1(k1_wellord2(sK3)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1729,plain,
    ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1728])).

cnf(c_20534,plain,
    ( v1_relat_1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))))) != iProver_top
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))))) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11227,c_1729])).

cnf(c_20535,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))))) = iProver_top
    | v1_relat_1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_20534])).

cnf(c_24,plain,
    ( r4_wellord1(X0,k2_wellord1(X0,X1))
    | r2_hidden(sK2(X1,X0),k3_relat_1(X0))
    | ~ r1_tarski(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1075,plain,
    ( r4_wellord1(X0,k2_wellord1(X0,X1)) = iProver_top
    | r2_hidden(sK2(X1,X0),k3_relat_1(X0)) = iProver_top
    | r1_tarski(X1,k3_relat_1(X0)) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1879,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) = iProver_top
    | r2_hidden(sK2(X1,k1_wellord2(X0)),X0) = iProver_top
    | r1_tarski(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
    | v2_wellord1(k1_wellord2(X0)) != iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_288,c_1075])).

cnf(c_1898,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) = iProver_top
    | r2_hidden(sK2(X1,k1_wellord2(X0)),X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | v2_wellord1(k1_wellord2(X0)) != iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1879,c_288])).

cnf(c_4994,plain,
    ( v2_wellord1(k1_wellord2(X0)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r2_hidden(sK2(X1,k1_wellord2(X0)),X0) = iProver_top
    | r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1898,c_70])).

cnf(c_4995,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) = iProver_top
    | r2_hidden(sK2(X1,k1_wellord2(X0)),X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | v2_wellord1(k1_wellord2(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4994])).

cnf(c_5004,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r2_hidden(sK2(sK3,k1_wellord2(sK4)),sK4) = iProver_top
    | r1_tarski(sK3,sK4) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1681,c_4995])).

cnf(c_16948,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r2_hidden(sK2(sK3,k1_wellord2(sK4)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5004,c_30,c_31,c_35,c_60,c_63])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1081,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16958,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = sK2(sK3,k1_wellord2(sK4))
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_16948,c_1081])).

cnf(c_27,negated_conjecture,
    ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_59,plain,
    ( r1_ordinal1(sK4,sK4)
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_355,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_390,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_359,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1452,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4)
    | k2_wellord2(k1_wellord2(sK3)) != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1454,plain,
    ( r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4)
    | ~ r1_ordinal1(sK4,sK4)
    | k2_wellord2(k1_wellord2(sK3)) != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1452])).

cnf(c_1556,plain,
    ( v2_wellord1(k1_wellord2(sK3))
    | ~ v3_ordinal1(sK4) ),
    inference(resolution,[status(thm)],[c_26,c_28])).

cnf(c_1557,plain,
    ( v2_wellord1(k1_wellord2(sK3)) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1556])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1080,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1078,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1869,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1080,c_1078])).

cnf(c_3586,plain,
    ( r4_wellord1(X0,k2_wellord1(X0,X1)) = iProver_top
    | r1_tarski(X1,k3_relat_1(X0)) != iProver_top
    | r1_tarski(k3_relat_1(X0),X2) != iProver_top
    | m1_subset_1(sK2(X1,X0),X2) = iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1075,c_1869])).

cnf(c_10976,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_tarski(k3_relat_1(k1_wellord2(sK4)),X0) != iProver_top
    | r1_tarski(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | m1_subset_1(sK2(sK3,k1_wellord2(sK4)),X0) = iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1681,c_3586])).

cnf(c_11102,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top
    | m1_subset_1(sK2(sK3,k1_wellord2(sK4)),X0) = iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10976,c_288])).

cnf(c_13186,plain,
    ( r1_tarski(sK4,X0) != iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | m1_subset_1(sK2(sK3,k1_wellord2(sK4)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11102,c_30,c_31,c_35,c_60,c_63,c_72])).

cnf(c_13187,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | m1_subset_1(sK2(sK3,k1_wellord2(sK4)),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_13186])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1098,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13195,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13187,c_1098])).

cnf(c_13221,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_tarski(sK4,sK4) != iProver_top
    | v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13195])).

cnf(c_13758,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13195,c_30,c_60,c_63,c_13221])).

cnf(c_13765,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13758,c_1077])).

cnf(c_13980,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top
    | v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13765,c_72,c_1729])).

cnf(c_11,plain,
    ( ~ r4_wellord1(X0,k1_wellord2(X1))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0)
    | ~ v3_ordinal1(X1)
    | k2_wellord2(X0) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1089,plain,
    ( k2_wellord2(X0) = X1
    | r4_wellord1(X0,k1_wellord2(X1)) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13986,plain,
    ( k2_wellord2(k1_wellord2(sK3)) = sK4
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_13980,c_1089])).

cnf(c_17639,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = sK2(sK3,k1_wellord2(sK4))
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16958,c_29,c_30,c_27,c_59,c_390,c_1454,c_1557,c_1729,c_13986])).

cnf(c_17645,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = sK2(sK3,k1_wellord2(sK4))
    | k2_wellord2(k1_wellord2(sK4)) = sK3
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17639,c_1089])).

cnf(c_17646,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = sK2(sK3,k1_wellord2(sK4))
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17639,c_1077])).

cnf(c_17943,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = sK2(sK3,k1_wellord2(sK4))
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17646,c_72,c_1729])).

cnf(c_17949,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = sK2(sK3,k1_wellord2(sK4))
    | k2_wellord2(k1_wellord2(sK3)) = sK4
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_17943,c_1089])).

cnf(c_19905,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = sK2(sK3,k1_wellord2(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17645,c_29,c_30,c_27,c_59,c_390,c_1454,c_1557,c_1729,c_17949])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1090,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v1_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_16956,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_tarski(sK2(sK3,k1_wellord2(sK4)),sK4) = iProver_top
    | v1_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_16948,c_1090])).

cnf(c_0,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_105,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_107,plain,
    ( v3_ordinal1(sK4) != iProver_top
    | v1_ordinal1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_17002,plain,
    ( r1_tarski(sK2(sK3,k1_wellord2(sK4)),sK4) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16956,c_30,c_107])).

cnf(c_17003,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_tarski(sK2(sK3,k1_wellord2(sK4)),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_17002])).

cnf(c_17008,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = k1_wellord2(sK2(sK3,k1_wellord2(sK4)))
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17003,c_1074])).

cnf(c_17222,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = k1_wellord2(sK2(sK3,k1_wellord2(sK4)))
    | k2_wellord2(k1_wellord2(sK4)) = sK3
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17008,c_1089])).

cnf(c_17223,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = k1_wellord2(sK2(sK3,k1_wellord2(sK4)))
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17008,c_1077])).

cnf(c_18426,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = k1_wellord2(sK2(sK3,k1_wellord2(sK4)))
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17223,c_72,c_1729])).

cnf(c_18432,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = k1_wellord2(sK2(sK3,k1_wellord2(sK4)))
    | k2_wellord2(k1_wellord2(sK3)) = sK4
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_18426,c_1089])).

cnf(c_19937,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = k1_wellord2(sK2(sK3,k1_wellord2(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17222,c_29,c_30,c_27,c_59,c_390,c_1454,c_1557,c_1729,c_18432])).

cnf(c_20538,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2(sK3,k1_wellord2(sK4)))) = iProver_top
    | v1_relat_1(k1_wellord2(sK2(sK3,k1_wellord2(sK4)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20535,c_19905,c_19937])).

cnf(c_1088,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_20542,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2(sK3,k1_wellord2(sK4)))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20538,c_1088])).

cnf(c_20545,plain,
    ( r4_wellord1(k1_wellord2(sK2(sK3,k1_wellord2(sK4))),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v1_relat_1(k1_wellord2(sK2(sK3,k1_wellord2(sK4)))) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20542,c_1077])).

cnf(c_21233,plain,
    ( v1_relat_1(k1_wellord2(sK2(sK3,k1_wellord2(sK4)))) != iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK2(sK3,k1_wellord2(sK4))),k1_wellord2(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20545,c_1729])).

cnf(c_21234,plain,
    ( r4_wellord1(k1_wellord2(sK2(sK3,k1_wellord2(sK4))),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v1_relat_1(k1_wellord2(sK2(sK3,k1_wellord2(sK4)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21233])).

cnf(c_21240,plain,
    ( r4_wellord1(k1_wellord2(sK2(sK3,k1_wellord2(sK4))),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21234,c_1088])).

cnf(c_21242,plain,
    ( k2_wellord2(k1_wellord2(sK2(sK3,k1_wellord2(sK4)))) = sK3
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v2_wellord1(k1_wellord2(sK2(sK3,k1_wellord2(sK4)))) != iProver_top
    | v1_relat_1(k1_wellord2(sK2(sK3,k1_wellord2(sK4)))) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_21240,c_1089])).

cnf(c_32,plain,
    ( r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_20544,plain,
    ( sK2(sK3,k1_wellord2(sK4)) = k2_wellord2(k1_wellord2(sK3))
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20542,c_1089])).

cnf(c_21820,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | sK2(sK3,k1_wellord2(sK4)) = k2_wellord2(k1_wellord2(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20544,c_29,c_30,c_27,c_59,c_390,c_1454,c_1557,c_1729,c_13986])).

cnf(c_21821,plain,
    ( sK2(sK3,k1_wellord2(sK4)) = k2_wellord2(k1_wellord2(sK3))
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_21820])).

cnf(c_21826,plain,
    ( sK2(sK3,k1_wellord2(sK4)) = k2_wellord2(k1_wellord2(sK3))
    | k2_wellord2(k1_wellord2(sK4)) = sK3
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_21821,c_1089])).

cnf(c_21827,plain,
    ( sK2(sK3,k1_wellord2(sK4)) = k2_wellord2(k1_wellord2(sK3))
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21821,c_1077])).

cnf(c_22025,plain,
    ( sK2(sK3,k1_wellord2(sK4)) = k2_wellord2(k1_wellord2(sK3))
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21827,c_72,c_1729])).

cnf(c_22031,plain,
    ( sK2(sK3,k1_wellord2(sK4)) = k2_wellord2(k1_wellord2(sK3))
    | k2_wellord2(k1_wellord2(sK3)) = sK4
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_22025,c_1089])).

cnf(c_22375,plain,
    ( sK2(sK3,k1_wellord2(sK4)) = k2_wellord2(k1_wellord2(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21826,c_29,c_30,c_27,c_59,c_390,c_1454,c_1557,c_1729,c_22031])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1086,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_ordinal1(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17010,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_ordinal1(sK2(sK3,k1_wellord2(sK4)),sK4) = iProver_top
    | v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_17003,c_1086])).

cnf(c_17245,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_ordinal1(sK2(sK3,k1_wellord2(sK4)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17010,c_29,c_30,c_27,c_59,c_390,c_1454,c_1557,c_1729,c_13986])).

cnf(c_22382,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_22375,c_17245])).

cnf(c_23046,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21242,c_32,c_22382])).

cnf(c_23052,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23046,c_1077])).

cnf(c_23368,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23052,c_72,c_1729])).

cnf(c_23373,plain,
    ( k2_wellord2(k1_wellord2(sK3)) = sK4
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_23368,c_1089])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23373,c_1729,c_1557,c_1454,c_390,c_59,c_27,c_30,c_29])).


%------------------------------------------------------------------------------
