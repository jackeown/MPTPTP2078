%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1636+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:02 EST 2020

% Result     : Theorem 6.47s
% Output     : CNFRefutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 671 expanded)
%              Number of clauses        :   96 ( 213 expanded)
%              Number of leaves         :   28 ( 158 expanded)
%              Depth                    :   26
%              Number of atoms          :  834 (2908 expanded)
%              Number of equality atoms :  165 ( 270 expanded)
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

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f21,f64])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r1_tarski(X1,k4_waybel_0(X0,X1))
            & r1_tarski(X1,k3_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r1_tarski(X1,k4_waybel_0(X0,X1))
              & r1_tarski(X1,k3_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k4_waybel_0(X0,X1))
            | ~ r1_tarski(X1,k3_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k4_waybel_0(X0,X1))
            | ~ r1_tarski(X1,k3_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k4_waybel_0(X0,X1))
            | ~ r1_tarski(X1,k3_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r1_tarski(sK13,k4_waybel_0(X0,sK13))
          | ~ r1_tarski(sK13,k3_waybel_0(X0,sK13)) )
        & m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
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

fof(f70,plain,
    ( ( ~ r1_tarski(sK13,k4_waybel_0(sK12,sK13))
      | ~ r1_tarski(sK13,k3_waybel_0(sK12,sK13)) )
    & m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(sK12)))
    & l1_orders_2(sK12)
    & v3_orders_2(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f35,f69,f68])).

fof(f113,plain,(
    m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(sK12))) ),
    inference(cnf_transformation,[],[f70])).

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

fof(f18,plain,(
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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ( k3_waybel_0(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f36,plain,(
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

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f18,f37,f36])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ( ( k3_waybel_0(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k3_waybel_0(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( k3_waybel_0(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k3_waybel_0(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f42])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k3_waybel_0(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f115,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k3_waybel_0(X1,X2))
      | ~ sP1(k3_waybel_0(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f72])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f112,plain,(
    l1_orders_2(sK12) ),
    inference(cnf_transformation,[],[f70])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0] :
      ( ( ( v3_orders_2(X0)
          | ~ r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v3_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f101,plain,(
    ! [X0] :
      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f111,plain,(
    v3_orders_2(sK12) ),
    inference(cnf_transformation,[],[f70])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK10(X0,X1),sK10(X0,X1)),X0)
        & r2_hidden(sK10(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f61,f62])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X3),X0)
      | ~ r2_hidden(X3,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f107,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f49,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X0)
          & r1_orders_2(X1,X6,X8)
          & m1_subset_1(X8,u1_struct_0(X1)) )
     => ( r2_hidden(sK6(X0,X1,X6),X0)
        & r1_orders_2(X1,X6,sK6(X0,X1,X6))
        & m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X0)
          & r1_orders_2(X1,X3,X5)
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r2_hidden(sK5(X0,X1,X2),X0)
        & r1_orders_2(X1,X3,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f46,f49,f48,f47])).

fof(f77,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X0)
      | ~ r1_orders_2(X1,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f65])).

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

fof(f19,plain,(
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

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ( k4_waybel_0(X0,X1) = X2
      <=> sP2(X1,X0,X2) )
      | ~ sP3(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f39,plain,(
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

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP3(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f19,f40,f39])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ( ( k4_waybel_0(X0,X1) = X2
          | ~ sP2(X1,X0,X2) )
        & ( sP2(X1,X0,X2)
          | k4_waybel_0(X0,X1) != X2 ) )
      | ~ sP3(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( k4_waybel_0(X1,X2) = X0
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | k4_waybel_0(X1,X2) != X0 ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f51])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | k4_waybel_0(X1,X2) != X0
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f116,plain,(
    ! [X2,X1] :
      ( sP2(X2,X1,k4_waybel_0(X1,X2))
      | ~ sP3(k4_waybel_0(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f84])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f58,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X0)
          & r1_orders_2(X1,X8,X6)
          & m1_subset_1(X8,u1_struct_0(X1)) )
     => ( r2_hidden(sK9(X0,X1,X6),X0)
        & r1_orders_2(X1,sK9(X0,X1,X6),X6)
        & m1_subset_1(sK9(X0,X1,X6),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X0)
          & r1_orders_2(X1,X5,X3)
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r2_hidden(sK8(X0,X1,X2),X0)
        & r1_orders_2(X1,sK8(X0,X1,X2),X3)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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

fof(f59,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f55,f58,f57,f56])).

fof(f89,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X0)
      | ~ r1_orders_2(X1,X7,X6)
      | ~ m1_subset_1(X7,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f114,plain,
    ( ~ r1_tarski(sK13,k4_waybel_0(sK12,sK13))
    | ~ r1_tarski(sK13,k3_waybel_0(sK12,sK13)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_29,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_6418,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK11(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(sK12))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_6413,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(sK12))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_12,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2,plain,
    ( ~ sP1(k3_waybel_0(X0,X1),X0,X1)
    | sP0(X1,X0,k3_waybel_0(X0,X1)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_553,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_orders_2(X3)
    | X1 != X3
    | X0 != X4
    | k3_waybel_0(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_2])).

cnf(c_554,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k3_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ l1_orders_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_34])).

cnf(c_559,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_558])).

cnf(c_42,negated_conjecture,
    ( l1_orders_2(sK12) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_780,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_559,c_42])).

cnf(c_781,plain,
    ( sP0(X0,sK12,k3_waybel_0(sK12,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK12))) ),
    inference(unflattening,[status(thm)],[c_780])).

cnf(c_6409,plain,
    ( sP0(X0,sK12,k3_waybel_0(sK12,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_38,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_6416,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_8321,plain,
    ( r2_hidden(X0,sK13) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6413,c_6416])).

cnf(c_37,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_6417,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_8497,plain,
    ( r2_hidden(X0,u1_struct_0(sK12)) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top
    | v1_xboole_0(u1_struct_0(sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8321,c_6417])).

cnf(c_46,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(sK12))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_39,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_6504,plain,
    ( ~ r2_hidden(X0,sK13)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(sK12)))
    | ~ v1_xboole_0(u1_struct_0(sK12)) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_6505,plain,
    ( r2_hidden(X0,sK13) != iProver_top
    | m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6504])).

cnf(c_13256,plain,
    ( r2_hidden(X0,sK13) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK12)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8497,c_46,c_6505])).

cnf(c_13257,plain,
    ( r2_hidden(X0,u1_struct_0(sK12)) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top ),
    inference(renaming,[status(thm)],[c_13256])).

cnf(c_31,plain,
    ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_43,negated_conjecture,
    ( v3_orders_2(sK12) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_520,plain,
    ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_43])).

cnf(c_521,plain,
    ( r1_relat_2(u1_orders_2(sK12),u1_struct_0(sK12))
    | ~ l1_orders_2(sK12) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_73,plain,
    ( r1_relat_2(u1_orders_2(sK12),u1_struct_0(sK12))
    | ~ v3_orders_2(sK12)
    | ~ l1_orders_2(sK12) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_523,plain,
    ( r1_relat_2(u1_orders_2(sK12),u1_struct_0(sK12)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_521,c_43,c_42,c_73])).

cnf(c_6412,plain,
    ( r1_relat_2(u1_orders_2(sK12),u1_struct_0(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_27,plain,
    ( ~ r1_relat_2(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X2),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_6420,plain,
    ( r1_relat_2(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X2),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10268,plain,
    ( r2_hidden(X0,u1_struct_0(sK12)) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK12)) = iProver_top
    | v1_relat_1(u1_orders_2(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6412,c_6420])).

cnf(c_724,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),X2)
    | ~ v1_relat_1(X2)
    | u1_orders_2(sK12) != X2
    | u1_struct_0(sK12) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_523])).

cnf(c_725,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK12))
    | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK12))
    | ~ v1_relat_1(u1_orders_2(sK12)) ),
    inference(unflattening,[status(thm)],[c_724])).

cnf(c_726,plain,
    ( r2_hidden(X0,u1_struct_0(sK12)) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK12)) = iProver_top
    | v1_relat_1(u1_orders_2(sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_36,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_834,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_42])).

cnf(c_835,plain,
    ( m1_subset_1(u1_orders_2(sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)))) ),
    inference(unflattening,[status(thm)],[c_834])).

cnf(c_6405,plain,
    ( m1_subset_1(u1_orders_2(sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_835])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6441,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7243,plain,
    ( v1_relat_1(u1_orders_2(sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6405,c_6441])).

cnf(c_10393,plain,
    ( r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK12)) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK12)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10268,c_726,c_7243])).

cnf(c_10394,plain,
    ( r2_hidden(X0,u1_struct_0(sK12)) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK12)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10393])).

cnf(c_32,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_859,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_42])).

cnf(c_860,plain,
    ( r1_orders_2(sK12,X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK12))
    | ~ m1_subset_1(X0,u1_struct_0(sK12))
    | ~ m1_subset_1(X1,u1_struct_0(sK12)) ),
    inference(unflattening,[status(thm)],[c_859])).

cnf(c_6403,plain,
    ( r1_orders_2(sK12,X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK12)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK12)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_860])).

cnf(c_10400,plain,
    ( r1_orders_2(sK12,X0,X0) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK12)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10394,c_6403])).

cnf(c_13264,plain,
    ( r1_orders_2(sK12,X0,X0) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13257,c_10400])).

cnf(c_22743,plain,
    ( r2_hidden(X0,sK13) != iProver_top
    | r1_orders_2(sK12,X0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13264,c_8321])).

cnf(c_22744,plain,
    ( r1_orders_2(sK12,X0,X0) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top ),
    inference(renaming,[status(thm)],[c_22743])).

cnf(c_8,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ sP0(X3,X0,X4)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_6435,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | sP0(X3,X0,X4) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(X1,X4) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_22750,plain,
    ( sP0(X0,sK12,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,sK13) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22744,c_6435])).

cnf(c_24634,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_waybel_0(sK12,X1)) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK12)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6409,c_22750])).

cnf(c_24674,plain,
    ( r2_hidden(X0,sK13) != iProver_top
    | r2_hidden(X0,k3_waybel_0(sK12,X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24634,c_8321])).

cnf(c_24675,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_waybel_0(sK12,X1)) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(renaming,[status(thm)],[c_24674])).

cnf(c_24680,plain,
    ( r2_hidden(X0,k3_waybel_0(sK12,sK13)) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_6413,c_24675])).

cnf(c_28,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_6419,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK11(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24694,plain,
    ( r1_tarski(X0,k3_waybel_0(sK12,sK13)) = iProver_top
    | r2_hidden(sK11(X0,k3_waybel_0(sK12,sK13)),sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_24680,c_6419])).

cnf(c_24708,plain,
    ( r1_tarski(sK13,k3_waybel_0(sK12,sK13)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6418,c_24694])).

cnf(c_24,plain,
    ( sP3(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_14,plain,
    ( ~ sP3(k4_waybel_0(X0,X1),X0,X1)
    | sP2(X1,X0,k4_waybel_0(X0,X1)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_604,plain,
    ( sP2(X0,X1,k4_waybel_0(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_orders_2(X3)
    | X1 != X3
    | X0 != X4
    | k4_waybel_0(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_14])).

cnf(c_605,plain,
    ( sP2(X0,X1,k4_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k4_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k4_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP2(X0,X1,k4_waybel_0(X1,X0))
    | ~ l1_orders_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_605,c_35])).

cnf(c_610,plain,
    ( sP2(X0,X1,k4_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_609])).

cnf(c_750,plain,
    ( sP2(X0,X1,k4_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_610,c_42])).

cnf(c_751,plain,
    ( sP2(X0,sK12,k4_waybel_0(sK12,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK12))) ),
    inference(unflattening,[status(thm)],[c_750])).

cnf(c_6411,plain,
    ( sP2(X0,sK12,k4_waybel_0(sK12,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_20,plain,
    ( ~ sP2(X0,X1,X2)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_6426,plain,
    ( sP2(X0,X1,X2) != iProver_top
    | r1_orders_2(X1,X3,X4) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(X4,X2) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12757,plain,
    ( r1_orders_2(sK12,X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,k4_waybel_0(sK12,X2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK12)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK12)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6411,c_6426])).

cnf(c_2189,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK12)))
    | X5 != X3
    | k4_waybel_0(sK12,X5) != X4
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_751])).

cnf(c_2190,plain,
    ( ~ r1_orders_2(sK12,X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,k4_waybel_0(sK12,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK12))
    | ~ m1_subset_1(X1,u1_struct_0(sK12))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK12))) ),
    inference(unflattening,[status(thm)],[c_2189])).

cnf(c_2206,plain,
    ( ~ r1_orders_2(sK12,X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,k4_waybel_0(sK12,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK12))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK12))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2190,c_38])).

cnf(c_2212,plain,
    ( r1_orders_2(sK12,X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,k4_waybel_0(sK12,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK12)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2206])).

cnf(c_15910,plain,
    ( r2_hidden(X1,k4_waybel_0(sK12,X2)) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_orders_2(sK12,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK12)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12757,c_2212])).

cnf(c_15911,plain,
    ( r1_orders_2(sK12,X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,k4_waybel_0(sK12,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK12)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK12))) != iProver_top ),
    inference(renaming,[status(thm)],[c_15910])).

cnf(c_15914,plain,
    ( r1_orders_2(sK12,X0,X1) != iProver_top
    | r2_hidden(X1,k4_waybel_0(sK12,sK13)) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6413,c_15911])).

cnf(c_22752,plain,
    ( r2_hidden(X0,k4_waybel_0(sK12,sK13)) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22744,c_15914])).

cnf(c_22850,plain,
    ( r2_hidden(X0,sK13) != iProver_top
    | r2_hidden(X0,k4_waybel_0(sK12,sK13)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22752,c_8321])).

cnf(c_22851,plain,
    ( r2_hidden(X0,k4_waybel_0(sK12,sK13)) = iProver_top
    | r2_hidden(X0,sK13) != iProver_top ),
    inference(renaming,[status(thm)],[c_22850])).

cnf(c_22857,plain,
    ( r1_tarski(X0,k4_waybel_0(sK12,sK13)) = iProver_top
    | r2_hidden(sK11(X0,k4_waybel_0(sK12,sK13)),sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_22851,c_6419])).

cnf(c_22871,plain,
    ( r1_tarski(sK13,k4_waybel_0(sK12,sK13)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6418,c_22857])).

cnf(c_40,negated_conjecture,
    ( ~ r1_tarski(sK13,k4_waybel_0(sK12,sK13))
    | ~ r1_tarski(sK13,k3_waybel_0(sK12,sK13)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_47,plain,
    ( r1_tarski(sK13,k4_waybel_0(sK12,sK13)) != iProver_top
    | r1_tarski(sK13,k3_waybel_0(sK12,sK13)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24708,c_22871,c_47])).


%------------------------------------------------------------------------------
