%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1625+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:00 EST 2020

% Result     : Theorem 11.52s
% Output     : CNFRefutation 11.52s
% Verified   : 
% Statistics : Number of formulae       :  234 (3027 expanded)
%              Number of clauses        :  144 ( 871 expanded)
%              Number of leaves         :   26 ( 772 expanded)
%              Depth                    :   24
%              Number of atoms          :  990 (15994 expanded)
%              Number of equality atoms :  205 ( 910 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X2)
                  & r2_hidden(X4,X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    | ~ r1_orders_2(X0,X4,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( r1_orders_2(X0,X4,X3)
                    & r1_orders_2(X0,X4,X2)
                    & r2_hidden(X4,X1)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    | ~ r1_orders_2(X0,X4,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( r1_orders_2(X0,X7,X6)
                    & r1_orders_2(X0,X7,X5)
                    & r2_hidden(X7,X1)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f56,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X7,X6)
          & r1_orders_2(X0,X7,X5)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,sK10(X0,X1,X5,X6),X6)
        & r1_orders_2(X0,sK10(X0,X1,X5,X6),X5)
        & r2_hidden(sK10(X0,X1,X5,X6),X1)
        & m1_subset_1(sK10(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X4,X3)
              | ~ r1_orders_2(X0,X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,X4,sK9(X0,X1))
            | ~ r1_orders_2(X0,X4,X2)
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  | ~ r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                | ~ r1_orders_2(X0,X4,sK8(X0,X1))
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK8(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ! [X4] :
              ( ~ r1_orders_2(X0,X4,sK9(X0,X1))
              | ~ r1_orders_2(X0,X4,sK8(X0,X1))
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X1)
          & m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
          & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( r1_orders_2(X0,sK10(X0,X1,X5,X6),X6)
                  & r1_orders_2(X0,sK10(X0,X1,X5,X6),X5)
                  & r2_hidden(sK10(X0,X1,X5,X6),X1)
                  & m1_subset_1(sK10(X0,X1,X5,X6),u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f53,f56,f55,f54])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( sP2(X0,X1)
      | ~ r1_orders_2(X0,X4,sK9(X0,X1))
      | ~ r1_orders_2(X0,X4,sK8(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
            & v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
              & v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
            | ~ v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
            | ~ v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
            | ~ v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(X0),sK12),X0)
          | ~ v1_waybel_0(k6_domain_1(u1_struct_0(X0),sK12),X0) )
        & m1_subset_1(sK12,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
              | ~ v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK11),X1),sK11)
            | ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK11),X1),sK11) )
          & m1_subset_1(X1,u1_struct_0(sK11)) )
      & l1_orders_2(sK11)
      & v3_orders_2(sK11)
      & ~ v2_struct_0(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK11),sK12),sK11)
      | ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK11),sK12),sK11) )
    & m1_subset_1(sK12,u1_struct_0(sK11))
    & l1_orders_2(sK11)
    & v3_orders_2(sK11)
    & ~ v2_struct_0(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f31,f60,f59])).

fof(f101,plain,(
    m1_subset_1(sK12,u1_struct_0(sK11)) ),
    inference(cnf_transformation,[],[f61])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f91,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f100,plain,(
    l1_orders_2(sK11) ),
    inference(cnf_transformation,[],[f61])).

fof(f98,plain,(
    ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    ! [X6,X0,X5,X1] :
      ( m1_subset_1(sK10(X0,X1,X5,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f105,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f103,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f63])).

fof(f104,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f103])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f99,plain,(
    v3_orders_2(sK11) ),
    inference(cnf_transformation,[],[f61])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X4,X3)
                                & r1_orders_2(X0,X4,X2)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ( v2_waybel_0(X1,X0)
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f16,f36,f35])).

fof(f89,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ( ( v2_waybel_0(X1,X0)
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | ~ v2_waybel_0(X1,X0) ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v2_waybel_0(X0,X1)
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | ~ v2_waybel_0(X0,X1) ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f50])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X0,X1)
      | ~ sP2(X1,X0)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X3,X4)
                                & r1_orders_2(X0,X2,X4)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ( v1_waybel_0(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X2,X4)
                  & r2_hidden(X4,X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f14,f33,f32])).

fof(f77,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ( ( v1_waybel_0(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_waybel_0(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_waybel_0(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v1_waybel_0(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f42])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X0,X1)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f102,plain,
    ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK11),sK12),sK11)
    | ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK11),sK12),sK11) ),
    inference(cnf_transformation,[],[f61])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    | ~ r1_orders_2(X0,X2,X4)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( r1_orders_2(X0,X3,X4)
                    & r1_orders_2(X0,X2,X4)
                    & r2_hidden(X4,X1)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    | ~ r1_orders_2(X0,X2,X4)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( r1_orders_2(X0,X6,X7)
                    & r1_orders_2(X0,X5,X7)
                    & r2_hidden(X7,X1)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f48,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X5,X7)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X6,sK7(X0,X1,X5,X6))
        & r1_orders_2(X0,X5,sK7(X0,X1,X5,X6))
        & r2_hidden(sK7(X0,X1,X5,X6),X1)
        & m1_subset_1(sK7(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X3,X4)
              | ~ r1_orders_2(X0,X2,X4)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,sK6(X0,X1),X4)
            | ~ r1_orders_2(X0,X2,X4)
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  | ~ r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                | ~ r1_orders_2(X0,sK5(X0,X1),X4)
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK5(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X4] :
              ( ~ r1_orders_2(X0,sK6(X0,X1),X4)
              | ~ r1_orders_2(X0,sK5(X0,X1),X4)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X1)
          & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
          & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( r1_orders_2(X0,X6,sK7(X0,X1,X5,X6))
                  & r1_orders_2(X0,X5,sK7(X0,X1,X5,X6))
                  & r2_hidden(sK7(X0,X1,X5,X6),X1)
                  & m1_subset_1(sK7(X0,X1,X5,X6),u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f45,f48,f47,f46])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_orders_2(X0,sK6(X0,X1),X4)
      | ~ r1_orders_2(X0,sK5(X0,X1),X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3779,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_4712,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(sK11,sK12,sK12)
    | X1 != sK12
    | X2 != sK12
    | X0 != sK11 ),
    inference(instantiation,[status(thm)],[c_3779])).

cnf(c_4950,plain,
    ( r1_orders_2(X0,sK12,X1)
    | ~ r1_orders_2(sK11,sK12,sK12)
    | X1 != sK12
    | X0 != sK11
    | sK12 != sK12 ),
    inference(instantiation,[status(thm)],[c_4712])).

cnf(c_50763,plain,
    ( r1_orders_2(X0,sK12,sK8(sK11,k1_tarski(sK12)))
    | ~ r1_orders_2(sK11,sK12,sK12)
    | X0 != sK11
    | sK8(sK11,k1_tarski(sK12)) != sK12
    | sK12 != sK12 ),
    inference(instantiation,[status(thm)],[c_4950])).

cnf(c_50770,plain,
    ( r1_orders_2(sK11,sK12,sK8(sK11,k1_tarski(sK12)))
    | ~ r1_orders_2(sK11,sK12,sK12)
    | sK8(sK11,k1_tarski(sK12)) != sK12
    | sK12 != sK12
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_50763])).

cnf(c_50678,plain,
    ( r1_orders_2(X0,sK12,sK9(sK11,k1_tarski(sK12)))
    | ~ r1_orders_2(sK11,sK12,sK12)
    | X0 != sK11
    | sK9(sK11,k1_tarski(sK12)) != sK12
    | sK12 != sK12 ),
    inference(instantiation,[status(thm)],[c_4950])).

cnf(c_50685,plain,
    ( r1_orders_2(sK11,sK12,sK9(sK11,k1_tarski(sK12)))
    | ~ r1_orders_2(sK11,sK12,sK12)
    | sK9(sK11,k1_tarski(sK12)) != sK12
    | sK12 != sK12
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_50678])).

cnf(c_18,plain,
    ( ~ r1_orders_2(X0,X1,sK8(X0,X2))
    | ~ r1_orders_2(X0,X1,sK9(X0,X2))
    | sP2(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4793,plain,
    ( ~ r1_orders_2(X0,X1,sK8(X0,k1_tarski(X2)))
    | ~ r1_orders_2(X0,X1,sK9(X0,k1_tarski(X2)))
    | sP2(X0,k1_tarski(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_10410,plain,
    ( ~ r1_orders_2(sK11,X0,sK8(sK11,k1_tarski(sK12)))
    | ~ r1_orders_2(sK11,X0,sK9(sK11,k1_tarski(sK12)))
    | sP2(sK11,k1_tarski(sK12))
    | ~ m1_subset_1(X0,u1_struct_0(sK11))
    | ~ r2_hidden(X0,k1_tarski(sK12)) ),
    inference(instantiation,[status(thm)],[c_4793])).

cnf(c_43521,plain,
    ( ~ r1_orders_2(sK11,sK12,sK8(sK11,k1_tarski(sK12)))
    | ~ r1_orders_2(sK11,sK12,sK9(sK11,k1_tarski(sK12)))
    | sP2(sK11,k1_tarski(sK12))
    | ~ m1_subset_1(sK12,u1_struct_0(sK11))
    | ~ r2_hidden(sK12,k1_tarski(sK12)) ),
    inference(instantiation,[status(thm)],[c_10410])).

cnf(c_19,plain,
    ( sP2(X0,X1)
    | r2_hidden(sK9(X0,X1),X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4311,plain,
    ( sP2(X0,X1) = iProver_top
    | r2_hidden(sK9(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK12,u1_struct_0(sK11)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_4302,plain,
    ( m1_subset_1(sK12,u1_struct_0(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_29,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_30,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_461,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_29,c_30])).

cnf(c_38,negated_conjecture,
    ( l1_orders_2(sK11) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_684,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_461,c_38])).

cnf(c_685,plain,
    ( v2_struct_0(sK11)
    | ~ v1_xboole_0(u1_struct_0(sK11)) ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_60,plain,
    ( v2_struct_0(sK11)
    | ~ l1_struct_0(sK11)
    | ~ v1_xboole_0(u1_struct_0(sK11)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_63,plain,
    ( l1_struct_0(sK11)
    | ~ l1_orders_2(sK11) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_687,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK11)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_685,c_40,c_38,c_60,c_63])).

cnf(c_697,plain,
    ( ~ m1_subset_1(X0,X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0)
    | u1_struct_0(sK11) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_687])).

cnf(c_698,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK11))
    | k6_domain_1(u1_struct_0(sK11),X0) = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_697])).

cnf(c_4300,plain,
    ( k6_domain_1(u1_struct_0(sK11),X0) = k1_tarski(X0)
    | m1_subset_1(X0,u1_struct_0(sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_4628,plain,
    ( k6_domain_1(u1_struct_0(sK11),sK12) = k1_tarski(sK12) ),
    inference(superposition,[status(thm)],[c_4302,c_4300])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK11) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_687])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK11))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK11),X0),k1_zfmisc_1(u1_struct_0(sK11))) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_4299,plain,
    ( m1_subset_1(X0,u1_struct_0(sK11)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK11),X0),k1_zfmisc_1(u1_struct_0(sK11))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_4677,plain,
    ( m1_subset_1(k1_tarski(sK12),k1_zfmisc_1(u1_struct_0(sK11))) = iProver_top
    | m1_subset_1(sK12,u1_struct_0(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4628,c_4299])).

cnf(c_44,plain,
    ( m1_subset_1(sK12,u1_struct_0(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4698,plain,
    ( m1_subset_1(k1_tarski(sK12),k1_zfmisc_1(u1_struct_0(sK11))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4677,c_44])).

cnf(c_35,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_4303,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5306,plain,
    ( m1_subset_1(X0,u1_struct_0(sK11)) = iProver_top
    | r2_hidden(X0,k1_tarski(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4698,c_4303])).

cnf(c_5344,plain,
    ( sP2(X0,k1_tarski(sK12)) = iProver_top
    | m1_subset_1(sK9(X0,k1_tarski(sK12)),u1_struct_0(sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4311,c_5306])).

cnf(c_26,plain,
    ( ~ sP2(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK10(X0,X1,X3,X2),u1_struct_0(X0))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4304,plain,
    ( sP2(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK10(X0,X1,X3,X2),u1_struct_0(X0)) = iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X3,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5586,plain,
    ( k6_domain_1(u1_struct_0(sK11),sK10(sK11,X0,X1,X2)) = k1_tarski(sK10(sK11,X0,X1,X2))
    | sP2(sK11,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK11)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK11)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4304,c_4300])).

cnf(c_6080,plain,
    ( k6_domain_1(u1_struct_0(sK11),sK10(sK11,X0,sK12,X1)) = k1_tarski(sK10(sK11,X0,sK12,X1))
    | sP2(sK11,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK11)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(sK12,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4302,c_5586])).

cnf(c_6169,plain,
    ( k6_domain_1(u1_struct_0(sK11),sK10(sK11,X0,sK12,sK9(X1,k1_tarski(sK12)))) = k1_tarski(sK10(sK11,X0,sK12,sK9(X1,k1_tarski(sK12))))
    | sP2(X1,k1_tarski(sK12)) = iProver_top
    | sP2(sK11,X0) != iProver_top
    | r2_hidden(sK9(X1,k1_tarski(sK12)),X0) != iProver_top
    | r2_hidden(sK12,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5344,c_6080])).

cnf(c_6607,plain,
    ( k6_domain_1(u1_struct_0(sK11),sK10(sK11,k1_tarski(sK12),sK12,sK9(X0,k1_tarski(sK12)))) = k1_tarski(sK10(sK11,k1_tarski(sK12),sK12,sK9(X0,k1_tarski(sK12))))
    | sP2(X0,k1_tarski(sK12)) = iProver_top
    | sP2(sK11,k1_tarski(sK12)) != iProver_top
    | r2_hidden(sK12,k1_tarski(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4311,c_6169])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_137,plain,
    ( ~ r2_hidden(sK11,k1_tarski(sK11))
    | sK11 = sK11 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_140,plain,
    ( r2_hidden(sK11,k1_tarski(sK11)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_34,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_39,negated_conjecture,
    ( v3_orders_2(sK11) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_605,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_39])).

cnf(c_606,plain,
    ( r3_orders_2(sK11,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK11))
    | ~ m1_subset_1(X1,u1_struct_0(sK11))
    | v2_struct_0(sK11)
    | ~ l1_orders_2(sK11) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_610,plain,
    ( r3_orders_2(sK11,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK11))
    | ~ m1_subset_1(X1,u1_struct_0(sK11)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_606,c_40,c_38])).

cnf(c_611,plain,
    ( r3_orders_2(sK11,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK11))
    | ~ m1_subset_1(X0,u1_struct_0(sK11)) ),
    inference(renaming,[status(thm)],[c_610])).

cnf(c_33,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_626,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_39])).

cnf(c_627,plain,
    ( ~ r3_orders_2(sK11,X0,X1)
    | r1_orders_2(sK11,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK11))
    | ~ m1_subset_1(X1,u1_struct_0(sK11))
    | v2_struct_0(sK11)
    | ~ l1_orders_2(sK11) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_631,plain,
    ( ~ r3_orders_2(sK11,X0,X1)
    | r1_orders_2(sK11,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK11))
    | ~ m1_subset_1(X1,u1_struct_0(sK11)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_40,c_38])).

cnf(c_632,plain,
    ( ~ r3_orders_2(sK11,X0,X1)
    | r1_orders_2(sK11,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK11))
    | ~ m1_subset_1(X0,u1_struct_0(sK11)) ),
    inference(renaming,[status(thm)],[c_631])).

cnf(c_728,plain,
    ( r1_orders_2(sK11,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK11))
    | ~ m1_subset_1(X0,u1_struct_0(sK11))
    | ~ m1_subset_1(X3,u1_struct_0(sK11))
    | ~ m1_subset_1(X1,u1_struct_0(sK11))
    | X0 != X3
    | X1 != X3
    | sK11 != sK11 ),
    inference(resolution_lifted,[status(thm)],[c_611,c_632])).

cnf(c_729,plain,
    ( r1_orders_2(sK11,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK11))
    | ~ m1_subset_1(X0,u1_struct_0(sK11)) ),
    inference(unflattening,[status(thm)],[c_728])).

cnf(c_3772,plain,
    ( r1_orders_2(sK11,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK11))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_729])).

cnf(c_3773,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_729])).

cnf(c_3771,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK11))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_729])).

cnf(c_3869,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK11))
    | r1_orders_2(sK11,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3772,c_3773,c_3771])).

cnf(c_3870,plain,
    ( r1_orders_2(sK11,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK11)) ),
    inference(renaming,[status(thm)],[c_3869])).

cnf(c_4597,plain,
    ( r1_orders_2(sK11,sK12,sK12)
    | ~ m1_subset_1(sK12,u1_struct_0(sK11)) ),
    inference(instantiation,[status(thm)],[c_3870])).

cnf(c_4598,plain,
    ( r1_orders_2(sK11,sK12,sK12) = iProver_top
    | m1_subset_1(sK12,u1_struct_0(sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4597])).

cnf(c_27,plain,
    ( sP3(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_16,plain,
    ( ~ sP3(X0,X1)
    | ~ sP2(X1,X0)
    | v2_waybel_0(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP1(X0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | v1_waybel_0(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_36,negated_conjecture,
    ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK11),sK12),sK11)
    | ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK11),sK12),sK11) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_480,plain,
    ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK11),sK12),sK11)
    | ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | k6_domain_1(u1_struct_0(sK11),sK12) != X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_36])).

cnf(c_481,plain,
    ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK11),sK12),sK11)
    | ~ sP1(k6_domain_1(u1_struct_0(sK11),sK12),sK11)
    | ~ sP0(sK11,k6_domain_1(u1_struct_0(sK11),sK12)) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_497,plain,
    ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK11),sK12),sK11)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ sP0(sK11,k6_domain_1(u1_struct_0(sK11),sK12))
    | ~ l1_orders_2(X1)
    | k6_domain_1(u1_struct_0(sK11),sK12) != X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_481])).

cnf(c_498,plain,
    ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK11),sK12),sK11)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK11),sK12),k1_zfmisc_1(u1_struct_0(sK11)))
    | ~ sP0(sK11,k6_domain_1(u1_struct_0(sK11),sK12))
    | ~ l1_orders_2(sK11) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_500,plain,
    ( ~ sP0(sK11,k6_domain_1(u1_struct_0(sK11),sK12))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK11),sK12),k1_zfmisc_1(u1_struct_0(sK11)))
    | ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK11),sK12),sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_498,c_38])).

cnf(c_501,plain,
    ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK11),sK12),sK11)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK11),sK12),k1_zfmisc_1(u1_struct_0(sK11)))
    | ~ sP0(sK11,k6_domain_1(u1_struct_0(sK11),sK12)) ),
    inference(renaming,[status(thm)],[c_500])).

cnf(c_519,plain,
    ( ~ sP3(X0,X1)
    | ~ sP2(X1,X0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK11),sK12),k1_zfmisc_1(u1_struct_0(sK11)))
    | ~ sP0(sK11,k6_domain_1(u1_struct_0(sK11),sK12))
    | k6_domain_1(u1_struct_0(sK11),sK12) != X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_501])).

cnf(c_520,plain,
    ( ~ sP3(k6_domain_1(u1_struct_0(sK11),sK12),sK11)
    | ~ sP2(sK11,k6_domain_1(u1_struct_0(sK11),sK12))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK11),sK12),k1_zfmisc_1(u1_struct_0(sK11)))
    | ~ sP0(sK11,k6_domain_1(u1_struct_0(sK11),sK12)) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_540,plain,
    ( ~ sP2(sK11,k6_domain_1(u1_struct_0(sK11),sK12))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK11),sK12),k1_zfmisc_1(u1_struct_0(sK11)))
    | ~ sP0(sK11,k6_domain_1(u1_struct_0(sK11),sK12))
    | ~ l1_orders_2(X1)
    | k6_domain_1(u1_struct_0(sK11),sK12) != X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_520])).

cnf(c_541,plain,
    ( ~ sP2(sK11,k6_domain_1(u1_struct_0(sK11),sK12))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK11),sK12),k1_zfmisc_1(u1_struct_0(sK11)))
    | ~ sP0(sK11,k6_domain_1(u1_struct_0(sK11),sK12))
    | ~ l1_orders_2(sK11) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_543,plain,
    ( ~ sP0(sK11,k6_domain_1(u1_struct_0(sK11),sK12))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK11),sK12),k1_zfmisc_1(u1_struct_0(sK11)))
    | ~ sP2(sK11,k6_domain_1(u1_struct_0(sK11),sK12)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_541,c_38])).

cnf(c_544,plain,
    ( ~ sP2(sK11,k6_domain_1(u1_struct_0(sK11),sK12))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK11),sK12),k1_zfmisc_1(u1_struct_0(sK11)))
    | ~ sP0(sK11,k6_domain_1(u1_struct_0(sK11),sK12)) ),
    inference(renaming,[status(thm)],[c_543])).

cnf(c_4301,plain,
    ( sP2(sK11,k6_domain_1(u1_struct_0(sK11),sK12)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK11),sK12),k1_zfmisc_1(u1_struct_0(sK11))) != iProver_top
    | sP0(sK11,k6_domain_1(u1_struct_0(sK11),sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_545,plain,
    ( sP2(sK11,k6_domain_1(u1_struct_0(sK11),sK12)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK11),sK12),k1_zfmisc_1(u1_struct_0(sK11))) != iProver_top
    | sP0(sK11,k6_domain_1(u1_struct_0(sK11),sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_4591,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK11),sK12),k1_zfmisc_1(u1_struct_0(sK11)))
    | ~ m1_subset_1(sK12,u1_struct_0(sK11)) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_4592,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK11),sK12),k1_zfmisc_1(u1_struct_0(sK11))) = iProver_top
    | m1_subset_1(sK12,u1_struct_0(sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4591])).

cnf(c_4763,plain,
    ( sP2(sK11,k6_domain_1(u1_struct_0(sK11),sK12)) != iProver_top
    | sP0(sK11,k6_domain_1(u1_struct_0(sK11),sK12)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4301,c_44,c_545,c_4592])).

cnf(c_4767,plain,
    ( sP2(sK11,k1_tarski(sK12)) != iProver_top
    | sP0(sK11,k1_tarski(sK12)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4763,c_4628])).

cnf(c_9,plain,
    ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
    | sP0(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_5265,plain,
    ( m1_subset_1(sK6(sK11,k1_tarski(sK12)),u1_struct_0(sK11))
    | sP0(sK11,k1_tarski(sK12)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5266,plain,
    ( m1_subset_1(sK6(sK11,k1_tarski(sK12)),u1_struct_0(sK11)) = iProver_top
    | sP0(sK11,k1_tarski(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5265])).

cnf(c_7,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK6(X0,X1),X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_5262,plain,
    ( sP0(sK11,k1_tarski(sK12))
    | r2_hidden(sK6(sK11,k1_tarski(sK12)),k1_tarski(sK12)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5274,plain,
    ( sP0(sK11,k1_tarski(sK12)) = iProver_top
    | r2_hidden(sK6(sK11,k1_tarski(sK12)),k1_tarski(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5262])).

cnf(c_8,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK5(X0,X1),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_5261,plain,
    ( sP0(sK11,k1_tarski(sK12))
    | r2_hidden(sK5(sK11,k1_tarski(sK12)),k1_tarski(sK12)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5276,plain,
    ( sP0(sK11,k1_tarski(sK12)) = iProver_top
    | r2_hidden(sK5(sK11,k1_tarski(sK12)),k1_tarski(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5261])).

cnf(c_4729,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK12))
    | X0 = sK12 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6979,plain,
    ( ~ r2_hidden(sK5(sK11,k1_tarski(sK12)),k1_tarski(sK12))
    | sK5(sK11,k1_tarski(sK12)) = sK12 ),
    inference(instantiation,[status(thm)],[c_4729])).

cnf(c_6980,plain,
    ( sK5(sK11,k1_tarski(sK12)) = sK12
    | r2_hidden(sK5(sK11,k1_tarski(sK12)),k1_tarski(sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6979])).

cnf(c_6992,plain,
    ( ~ r2_hidden(sK6(sK11,k1_tarski(sK12)),k1_tarski(sK12))
    | sK6(sK11,k1_tarski(sK12)) = sK12 ),
    inference(instantiation,[status(thm)],[c_4729])).

cnf(c_6993,plain,
    ( sK6(sK11,k1_tarski(sK12)) = sK12
    | r2_hidden(sK6(sK11,k1_tarski(sK12)),k1_tarski(sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6992])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,sK5(X0,X1),X2)
    | ~ r1_orders_2(X0,sK6(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sP0(X0,X1)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5263,plain,
    ( ~ r1_orders_2(sK11,sK5(sK11,k1_tarski(sK12)),X0)
    | ~ r1_orders_2(sK11,sK6(sK11,k1_tarski(sK12)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK11))
    | sP0(sK11,k1_tarski(sK12))
    | ~ r2_hidden(X0,k1_tarski(sK12)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_7637,plain,
    ( ~ r1_orders_2(sK11,sK5(sK11,k1_tarski(sK12)),sK6(sK11,k1_tarski(sK12)))
    | ~ r1_orders_2(sK11,sK6(sK11,k1_tarski(sK12)),sK6(sK11,k1_tarski(sK12)))
    | ~ m1_subset_1(sK6(sK11,k1_tarski(sK12)),u1_struct_0(sK11))
    | sP0(sK11,k1_tarski(sK12))
    | ~ r2_hidden(sK6(sK11,k1_tarski(sK12)),k1_tarski(sK12)) ),
    inference(instantiation,[status(thm)],[c_5263])).

cnf(c_7638,plain,
    ( r1_orders_2(sK11,sK5(sK11,k1_tarski(sK12)),sK6(sK11,k1_tarski(sK12))) != iProver_top
    | r1_orders_2(sK11,sK6(sK11,k1_tarski(sK12)),sK6(sK11,k1_tarski(sK12))) != iProver_top
    | m1_subset_1(sK6(sK11,k1_tarski(sK12)),u1_struct_0(sK11)) != iProver_top
    | sP0(sK11,k1_tarski(sK12)) = iProver_top
    | r2_hidden(sK6(sK11,k1_tarski(sK12)),k1_tarski(sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7637])).

cnf(c_4320,plain,
    ( sP0(X0,X1) = iProver_top
    | r2_hidden(sK6(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5927,plain,
    ( m1_subset_1(sK6(X0,k1_tarski(sK12)),u1_struct_0(sK11)) = iProver_top
    | sP0(X0,k1_tarski(sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4320,c_5306])).

cnf(c_4297,plain,
    ( r1_orders_2(sK11,X0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK11)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3772])).

cnf(c_3795,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3773])).

cnf(c_3796,plain,
    ( r1_orders_2(sK11,X0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK11)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3772])).

cnf(c_4298,plain,
    ( m1_subset_1(X0,u1_struct_0(sK11)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3771])).

cnf(c_4611,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4302,c_4298])).

cnf(c_4704,plain,
    ( m1_subset_1(X0,u1_struct_0(sK11)) != iProver_top
    | r1_orders_2(sK11,X0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4297,c_3795,c_3796,c_4611])).

cnf(c_4705,plain,
    ( r1_orders_2(sK11,X0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK11)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4704])).

cnf(c_11490,plain,
    ( r1_orders_2(sK11,sK6(X0,k1_tarski(sK12)),sK6(X0,k1_tarski(sK12))) = iProver_top
    | sP0(X0,k1_tarski(sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5927,c_4705])).

cnf(c_11590,plain,
    ( r1_orders_2(sK11,sK6(sK11,k1_tarski(sK12)),sK6(sK11,k1_tarski(sK12))) = iProver_top
    | sP0(sK11,k1_tarski(sK12)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11490])).

cnf(c_11671,plain,
    ( r1_orders_2(X0,sK5(sK11,k1_tarski(sK12)),X1)
    | ~ r1_orders_2(sK11,sK12,sK12)
    | X1 != sK12
    | X0 != sK11
    | sK5(sK11,k1_tarski(sK12)) != sK12 ),
    inference(instantiation,[status(thm)],[c_4712])).

cnf(c_31538,plain,
    ( r1_orders_2(X0,sK5(sK11,k1_tarski(sK12)),sK6(sK11,k1_tarski(sK12)))
    | ~ r1_orders_2(sK11,sK12,sK12)
    | X0 != sK11
    | sK5(sK11,k1_tarski(sK12)) != sK12
    | sK6(sK11,k1_tarski(sK12)) != sK12 ),
    inference(instantiation,[status(thm)],[c_11671])).

cnf(c_31539,plain,
    ( X0 != sK11
    | sK5(sK11,k1_tarski(sK12)) != sK12
    | sK6(sK11,k1_tarski(sK12)) != sK12
    | r1_orders_2(X0,sK5(sK11,k1_tarski(sK12)),sK6(sK11,k1_tarski(sK12))) = iProver_top
    | r1_orders_2(sK11,sK12,sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31538])).

cnf(c_31541,plain,
    ( sK5(sK11,k1_tarski(sK12)) != sK12
    | sK6(sK11,k1_tarski(sK12)) != sK12
    | sK11 != sK11
    | r1_orders_2(sK11,sK5(sK11,k1_tarski(sK12)),sK6(sK11,k1_tarski(sK12))) = iProver_top
    | r1_orders_2(sK11,sK12,sK12) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31539])).

cnf(c_35718,plain,
    ( sP2(sK11,k1_tarski(sK12)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6607,c_44,c_137,c_140,c_4598,c_4767,c_5266,c_5274,c_5276,c_6980,c_6993,c_7638,c_11590,c_31541])).

cnf(c_35720,plain,
    ( ~ sP2(sK11,k1_tarski(sK12)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_35718])).

cnf(c_18144,plain,
    ( ~ r2_hidden(sK8(sK11,k1_tarski(sK12)),k1_tarski(sK12))
    | sK8(sK11,k1_tarski(sK12)) = sK12 ),
    inference(instantiation,[status(thm)],[c_4729])).

cnf(c_18145,plain,
    ( sK8(sK11,k1_tarski(sK12)) = sK12
    | r2_hidden(sK8(sK11,k1_tarski(sK12)),k1_tarski(sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18144])).

cnf(c_18110,plain,
    ( ~ r2_hidden(sK9(sK11,k1_tarski(sK12)),k1_tarski(sK12))
    | sK9(sK11,k1_tarski(sK12)) = sK12 ),
    inference(instantiation,[status(thm)],[c_4729])).

cnf(c_18111,plain,
    ( sK9(sK11,k1_tarski(sK12)) = sK12
    | r2_hidden(sK9(sK11,k1_tarski(sK12)),k1_tarski(sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18110])).

cnf(c_4774,plain,
    ( sP2(X0,k1_tarski(X1))
    | r2_hidden(sK9(X0,k1_tarski(X1)),k1_tarski(X1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_10398,plain,
    ( sP2(sK11,k1_tarski(sK12))
    | r2_hidden(sK9(sK11,k1_tarski(sK12)),k1_tarski(sK12)) ),
    inference(instantiation,[status(thm)],[c_4774])).

cnf(c_10408,plain,
    ( sP2(sK11,k1_tarski(sK12)) = iProver_top
    | r2_hidden(sK9(sK11,k1_tarski(sK12)),k1_tarski(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10398])).

cnf(c_20,plain,
    ( sP2(X0,X1)
    | r2_hidden(sK8(X0,X1),X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4773,plain,
    ( sP2(X0,k1_tarski(X1))
    | r2_hidden(sK8(X0,k1_tarski(X1)),k1_tarski(X1)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_10399,plain,
    ( sP2(sK11,k1_tarski(sK12))
    | r2_hidden(sK8(sK11,k1_tarski(sK12)),k1_tarski(sK12)) ),
    inference(instantiation,[status(thm)],[c_4773])).

cnf(c_10406,plain,
    ( sP2(sK11,k1_tarski(sK12)) = iProver_top
    | r2_hidden(sK8(sK11,k1_tarski(sK12)),k1_tarski(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10399])).

cnf(c_5334,plain,
    ( r2_hidden(sK12,k1_tarski(sK12)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3775,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4735,plain,
    ( sK12 = sK12 ),
    inference(instantiation,[status(thm)],[c_3775])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50770,c_50685,c_43521,c_35720,c_35718,c_18145,c_18111,c_10408,c_10406,c_5334,c_4735,c_4597,c_140,c_137,c_37])).


%------------------------------------------------------------------------------
