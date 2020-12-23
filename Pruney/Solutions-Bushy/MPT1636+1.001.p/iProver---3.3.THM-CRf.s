%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1636+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:02 EST 2020

% Result     : Theorem 7.16s
% Output     : CNFRefutation 7.16s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 480 expanded)
%              Number of clauses        :   83 ( 154 expanded)
%              Number of leaves         :   27 ( 112 expanded)
%              Depth                    :   24
%              Number of atoms          :  803 (2173 expanded)
%              Number of equality atoms :  150 ( 233 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f60,f61])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r1_tarski(X1,k4_waybel_0(X0,X1))
            & r1_tarski(X1,k3_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r1_tarski(X1,k4_waybel_0(X0,X1))
              & r1_tarski(X1,k3_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k4_waybel_0(X0,X1))
            | ~ r1_tarski(X1,k3_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k4_waybel_0(X0,X1))
            | ~ r1_tarski(X1,k3_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k4_waybel_0(X0,X1))
            | ~ r1_tarski(X1,k3_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r1_tarski(sK13,k4_waybel_0(X0,sK13))
          | ~ r1_tarski(sK13,k3_waybel_0(X0,sK13)) )
        & m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k4_waybel_0(X0,X1))
              | ~ r1_tarski(X1,k3_waybel_0(X0,X1)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k4_waybel_0(sK12,X1))
            | ~ r1_tarski(X1,k3_waybel_0(sK12,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK12))) )
      & l1_orders_2(sK12)
      & v3_orders_2(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ( ~ r1_tarski(sK13,k4_waybel_0(sK12,sK13))
      | ~ r1_tarski(sK13,k3_waybel_0(sK12,sK13)) )
    & m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(sK12)))
    & l1_orders_2(sK12)
    & v3_orders_2(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f30,f67,f66])).

fof(f112,plain,(
    m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(sK12))) ),
    inference(cnf_transformation,[],[f68])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ( k3_waybel_0(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> ? [X4] :
                ( r2_hidden(X4,X1)
                & r1_orders_2(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f16,f32,f31])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ( ( k3_waybel_0(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k3_waybel_0(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( k3_waybel_0(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k3_waybel_0(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k3_waybel_0(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k3_waybel_0(X1,X2))
      | ~ sP1(k3_waybel_0(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f70])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f111,plain,(
    l1_orders_2(sK12) ),
    inference(cnf_transformation,[],[f68])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X2),X0)
                | ~ r2_hidden(X2,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK10(X0,X1),sK10(X0,X1)),X0)
        & r2_hidden(sK10(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK10(X0,X1),sK10(X0,X1)),X0)
              & r2_hidden(sK10(X0,X1),X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f56,f57])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X3),X0)
      | ~ r2_hidden(X3,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f110,plain,(
    v3_orders_2(sK12) ),
    inference(cnf_transformation,[],[f68])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f106,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v3_orders_2(X0)
          | ~ r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v3_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f100,plain,(
    ! [X0] :
      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r1_orders_2(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r1_orders_2(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r1_orders_2(X0,X3,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
              & ( ? [X4] :
                    ( r2_hidden(X4,X1)
                    & r1_orders_2(X0,X3,X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r1_orders_2(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r1_orders_2(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r1_orders_2(X0,X3,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
              & ( ? [X4] :
                    ( r2_hidden(X4,X1)
                    & r1_orders_2(X0,X3,X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X0)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r2_hidden(X5,X0)
                  & r1_orders_2(X1,X3,X5)
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ! [X7] :
                    ( ~ r2_hidden(X7,X0)
                    | ~ r1_orders_2(X1,X6,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(X1)) ) )
              & ( ? [X8] :
                    ( r2_hidden(X8,X0)
                    & r1_orders_2(X1,X6,X8)
                    & m1_subset_1(X8,u1_struct_0(X1)) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f44,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X0)
          & r1_orders_2(X1,X6,X8)
          & m1_subset_1(X8,u1_struct_0(X1)) )
     => ( r2_hidden(sK6(X0,X1,X6),X0)
        & r1_orders_2(X1,X6,sK6(X0,X1,X6))
        & m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X0)
          & r1_orders_2(X1,X3,X5)
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r2_hidden(sK5(X0,X1,X2),X0)
        & r1_orders_2(X1,X3,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X0)
                & r1_orders_2(X1,X3,X5)
                & m1_subset_1(X5,u1_struct_0(X1)) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X0)
              | ~ r1_orders_2(X1,sK4(X0,X1,X2),X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X0)
              & r1_orders_2(X1,sK4(X0,X1,X2),X5)
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | r2_hidden(sK4(X0,X1,X2),X2) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r1_orders_2(X1,sK4(X0,X1,X2),X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X0)
              & r1_orders_2(X1,sK4(X0,X1,X2),sK5(X0,X1,X2))
              & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
            | r2_hidden(sK4(X0,X1,X2),X2) )
          & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ! [X7] :
                    ( ~ r2_hidden(X7,X0)
                    | ~ r1_orders_2(X1,X6,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(X1)) ) )
              & ( ( r2_hidden(sK6(X0,X1,X6),X0)
                  & r1_orders_2(X1,X6,sK6(X0,X1,X6))
                  & m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X1)) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f41,f44,f43,f42])).

fof(f75,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X0)
      | ~ r1_orders_2(X1,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ( k4_waybel_0(X0,X1) = X2
      <=> sP2(X1,X0,X2) )
      | ~ sP3(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> ? [X4] :
                ( r2_hidden(X4,X1)
                & r1_orders_2(X0,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP3(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f17,f35,f34])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ( ( k4_waybel_0(X0,X1) = X2
          | ~ sP2(X1,X0,X2) )
        & ( sP2(X1,X0,X2)
          | k4_waybel_0(X0,X1) != X2 ) )
      | ~ sP3(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( k4_waybel_0(X1,X2) = X0
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | k4_waybel_0(X1,X2) != X0 ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f46])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | k4_waybel_0(X1,X2) != X0
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f115,plain,(
    ! [X2,X1] :
      ( sP2(X2,X1,k4_waybel_0(X1,X2))
      | ~ sP3(k4_waybel_0(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f82])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r1_orders_2(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r1_orders_2(X0,X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r1_orders_2(X0,X4,X3)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
              & ( ? [X4] :
                    ( r2_hidden(X4,X1)
                    & r1_orders_2(X0,X4,X3)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r1_orders_2(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r1_orders_2(X0,X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r1_orders_2(X0,X4,X3)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
              & ( ? [X4] :
                    ( r2_hidden(X4,X1)
                    & r1_orders_2(X0,X4,X3)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(flattening,[],[f48])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X0)
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r2_hidden(X5,X0)
                  & r1_orders_2(X1,X5,X3)
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ! [X7] :
                    ( ~ r2_hidden(X7,X0)
                    | ~ r1_orders_2(X1,X7,X6)
                    | ~ m1_subset_1(X7,u1_struct_0(X1)) ) )
              & ( ? [X8] :
                    ( r2_hidden(X8,X0)
                    & r1_orders_2(X1,X8,X6)
                    & m1_subset_1(X8,u1_struct_0(X1)) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f49])).

fof(f53,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X0)
          & r1_orders_2(X1,X8,X6)
          & m1_subset_1(X8,u1_struct_0(X1)) )
     => ( r2_hidden(sK9(X0,X1,X6),X0)
        & r1_orders_2(X1,sK9(X0,X1,X6),X6)
        & m1_subset_1(sK9(X0,X1,X6),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X0)
          & r1_orders_2(X1,X5,X3)
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r2_hidden(sK8(X0,X1,X2),X0)
        & r1_orders_2(X1,sK8(X0,X1,X2),X3)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r1_orders_2(X1,X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X0)
                & r1_orders_2(X1,X5,X3)
                & m1_subset_1(X5,u1_struct_0(X1)) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X0)
              | ~ r1_orders_2(X1,X4,sK7(X0,X1,X2))
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X0)
              & r1_orders_2(X1,X5,sK7(X0,X1,X2))
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | r2_hidden(sK7(X0,X1,X2),X2) )
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r1_orders_2(X1,X4,sK7(X0,X1,X2))
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK8(X0,X1,X2),X0)
              & r1_orders_2(X1,sK8(X0,X1,X2),sK7(X0,X1,X2))
              & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
            | r2_hidden(sK7(X0,X1,X2),X2) )
          & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ! [X7] :
                    ( ~ r2_hidden(X7,X0)
                    | ~ r1_orders_2(X1,X7,X6)
                    | ~ m1_subset_1(X7,u1_struct_0(X1)) ) )
              & ( ( r2_hidden(sK9(X0,X1,X6),X0)
                  & r1_orders_2(X1,sK9(X0,X1,X6),X6)
                  & m1_subset_1(sK9(X0,X1,X6),u1_struct_0(X1)) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f50,f53,f52,f51])).

fof(f87,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X0)
      | ~ r1_orders_2(X1,X7,X6)
      | ~ m1_subset_1(X7,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f113,plain,
    ( ~ r1_tarski(sK13,k4_waybel_0(sK12,sK13))
    | ~ r1_tarski(sK13,k3_waybel_0(sK12,sK13)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_6869,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK11(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(sK12))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_6863,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(sK12))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_12,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2,plain,
    ( ~ sP1(k3_waybel_0(X0,X1),X0,X1)
    | sP0(X1,X0,k3_waybel_0(X0,X1)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_643,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_orders_2(X3)
    | X1 != X3
    | X0 != X4
    | k3_waybel_0(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_2])).

cnf(c_644,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k3_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ l1_orders_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_644,c_35])).

cnf(c_649,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_648])).

cnf(c_43,negated_conjecture,
    ( l1_orders_2(sK12) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_870,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_649,c_43])).

cnf(c_871,plain,
    ( sP0(X0,sK12,k3_waybel_0(sK12,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK12))) ),
    inference(unflattening,[status(thm)],[c_870])).

cnf(c_6859,plain,
    ( sP0(X0,sK12,k3_waybel_0(sK12,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_871])).

cnf(c_39,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_6866,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_7316,plain,
    ( r1_tarski(sK13,u1_struct_0(sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6863,c_6866])).

cnf(c_30,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_6868,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8072,plain,
    ( r2_hidden(X0,u1_struct_0(sK12)) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_7316,c_6868])).

cnf(c_27,plain,
    ( ~ r1_relat_2(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X2),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_6871,plain,
    ( r1_relat_2(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X2),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_9510,plain,
    ( r1_relat_2(X0,u1_struct_0(sK12)) != iProver_top
    | r2_hidden(X1,sK13) != iProver_top
    | r2_hidden(k4_tarski(X1,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8072,c_6871])).

cnf(c_33,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_949,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_43])).

cnf(c_950,plain,
    ( r1_orders_2(sK12,X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK12))
    | ~ m1_subset_1(X0,u1_struct_0(sK12))
    | ~ m1_subset_1(X1,u1_struct_0(sK12)) ),
    inference(unflattening,[status(thm)],[c_949])).

cnf(c_6853,plain,
    ( r1_orders_2(sK12,X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK12)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK12)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_950])).

cnf(c_21872,plain,
    ( r1_orders_2(sK12,X0,X0) = iProver_top
    | r1_relat_2(u1_orders_2(sK12),u1_struct_0(sK12)) != iProver_top
    | r2_hidden(X0,sK13) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK12)) != iProver_top
    | v1_relat_1(u1_orders_2(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9510,c_6853])).

cnf(c_44,negated_conjecture,
    ( v3_orders_2(sK12) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_45,plain,
    ( v3_orders_2(sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_46,plain,
    ( l1_orders_2(sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_37,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_58,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_60,plain,
    ( m1_subset_1(u1_orders_2(sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)))) = iProver_top
    | l1_orders_2(sK12) != iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_32,plain,
    ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_73,plain,
    ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_75,plain,
    ( r1_relat_2(u1_orders_2(sK12),u1_struct_0(sK12)) = iProver_top
    | v3_orders_2(sK12) != iProver_top
    | l1_orders_2(sK12) != iProver_top ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_7253,plain,
    ( ~ m1_subset_1(u1_orders_2(sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12))))
    | v1_relat_1(u1_orders_2(sK12)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7254,plain,
    ( m1_subset_1(u1_orders_2(sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)))) != iProver_top
    | v1_relat_1(u1_orders_2(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7253])).

cnf(c_40,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_6865,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_7982,plain,
    ( r2_hidden(X0,sK13) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6863,c_6865])).

cnf(c_22513,plain,
    ( r1_orders_2(sK12,X0,X0) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21872,c_45,c_46,c_60,c_75,c_7254,c_7982])).

cnf(c_8,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ sP0(X3,X0,X4)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_6886,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | sP0(X3,X0,X4) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(X1,X4) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_22522,plain,
    ( sP0(X0,sK12,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,sK13) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22513,c_6886])).

cnf(c_30180,plain,
    ( sP0(X0,sK12,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,sK13) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_22522,c_7982])).

cnf(c_30182,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_waybel_0(sK12,X1)) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6859,c_30180])).

cnf(c_30582,plain,
    ( r2_hidden(X0,k3_waybel_0(sK12,sK13)) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_6863,c_30182])).

cnf(c_28,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_6870,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK11(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_30651,plain,
    ( r1_tarski(X0,k3_waybel_0(sK12,sK13)) = iProver_top
    | r2_hidden(sK11(X0,k3_waybel_0(sK12,sK13)),sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_30582,c_6870])).

cnf(c_30700,plain,
    ( r1_tarski(sK13,k3_waybel_0(sK12,sK13)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6869,c_30651])).

cnf(c_24,plain,
    ( sP3(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_14,plain,
    ( ~ sP3(k4_waybel_0(X0,X1),X0,X1)
    | sP2(X1,X0,k4_waybel_0(X0,X1)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_694,plain,
    ( sP2(X0,X1,k4_waybel_0(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_orders_2(X3)
    | X1 != X3
    | X0 != X4
    | k4_waybel_0(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_14])).

cnf(c_695,plain,
    ( sP2(X0,X1,k4_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k4_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k4_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_699,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP2(X0,X1,k4_waybel_0(X1,X0))
    | ~ l1_orders_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_36])).

cnf(c_700,plain,
    ( sP2(X0,X1,k4_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_699])).

cnf(c_840,plain,
    ( sP2(X0,X1,k4_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_700,c_43])).

cnf(c_841,plain,
    ( sP2(X0,sK12,k4_waybel_0(sK12,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK12))) ),
    inference(unflattening,[status(thm)],[c_840])).

cnf(c_6861,plain,
    ( sP2(X0,sK12,k4_waybel_0(sK12,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_20,plain,
    ( ~ sP2(X0,X1,X2)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_6877,plain,
    ( sP2(X0,X1,X2) != iProver_top
    | r1_orders_2(X1,X3,X4) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(X4,X2) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11071,plain,
    ( r1_orders_2(sK12,X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,k4_waybel_0(sK12,X2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK12)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK12)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6861,c_6877])).

cnf(c_2279,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK12)))
    | X5 != X3
    | k4_waybel_0(sK12,X5) != X4
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_841])).

cnf(c_2280,plain,
    ( ~ r1_orders_2(sK12,X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,k4_waybel_0(sK12,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK12))
    | ~ m1_subset_1(X1,u1_struct_0(sK12))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK12))) ),
    inference(unflattening,[status(thm)],[c_2279])).

cnf(c_2296,plain,
    ( ~ r1_orders_2(sK12,X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,k4_waybel_0(sK12,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK12))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK12))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2280,c_40])).

cnf(c_2302,plain,
    ( r1_orders_2(sK12,X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,k4_waybel_0(sK12,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK12)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2296])).

cnf(c_13419,plain,
    ( r2_hidden(X1,k4_waybel_0(sK12,X2)) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_orders_2(sK12,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK12)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11071,c_2302])).

cnf(c_13420,plain,
    ( r1_orders_2(sK12,X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,k4_waybel_0(sK12,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK12)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13419])).

cnf(c_13429,plain,
    ( r1_orders_2(sK12,X0,X1) != iProver_top
    | r2_hidden(X1,k4_waybel_0(sK12,sK13)) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6863,c_13420])).

cnf(c_22524,plain,
    ( r2_hidden(X0,k4_waybel_0(sK12,sK13)) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22513,c_13429])).

cnf(c_22582,plain,
    ( r2_hidden(X0,sK13) != iProver_top
    | r2_hidden(X0,k4_waybel_0(sK12,sK13)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22524,c_7982])).

cnf(c_22583,plain,
    ( r2_hidden(X0,k4_waybel_0(sK12,sK13)) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top ),
    inference(renaming,[status(thm)],[c_22582])).

cnf(c_22592,plain,
    ( r1_tarski(X0,k4_waybel_0(sK12,sK13)) = iProver_top
    | r2_hidden(sK11(X0,k4_waybel_0(sK12,sK13)),sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_22583,c_6870])).

cnf(c_23356,plain,
    ( r1_tarski(sK13,k4_waybel_0(sK12,sK13)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6869,c_22592])).

cnf(c_41,negated_conjecture,
    ( ~ r1_tarski(sK13,k4_waybel_0(sK12,sK13))
    | ~ r1_tarski(sK13,k3_waybel_0(sK12,sK13)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_48,plain,
    ( r1_tarski(sK13,k4_waybel_0(sK12,sK13)) != iProver_top
    | r1_tarski(sK13,k3_waybel_0(sK12,sK13)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30700,c_23356,c_48])).


%------------------------------------------------------------------------------
