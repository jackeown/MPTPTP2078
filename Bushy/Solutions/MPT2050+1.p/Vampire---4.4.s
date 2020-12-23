%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t9_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:53 EDT 2019

% Result     : Theorem 3.73s
% Output     : Refutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  157 (1598 expanded)
%              Number of leaves         :   29 ( 619 expanded)
%              Depth                    :   28
%              Number of atoms          : 1135 (12782 expanded)
%              Number of equality atoms :  117 ( 301 expanded)
%              Maximal formula depth    :   26 (   9 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8737,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8446,f176])).

fof(f176,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',dt_o_0_0_xboole_0)).

fof(f8446,plain,(
    ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f8443,f277])).

fof(f277,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f168,f169,f183])).

fof(f183,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f60,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',fc2_struct_0)).

fof(f169,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f138])).

fof(f138,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK2)
    & m1_yellow19(sK2,sK0,sK1)
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f62,f137,f136,f135])).

fof(f135,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_waybel_0(X0,X1,X2)
                & m1_yellow19(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_waybel_0(sK0,X1,X2)
              & m1_yellow19(X2,sK0,X1) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f136,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_waybel_0(X0,X1,X2)
              & m1_yellow19(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r1_waybel_0(X0,sK1,X2)
            & m1_yellow19(X2,X0,sK1) )
        & l1_waybel_0(sK1,X0)
        & v7_waybel_0(sK1)
        & v4_orders_2(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_waybel_0(X0,X1,X2)
          & m1_yellow19(X2,X0,X1) )
     => ( ~ r1_waybel_0(X0,X1,sK2)
        & m1_yellow19(sK2,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_waybel_0(X0,X1,X2)
              & m1_yellow19(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_waybel_0(X0,X1,X2)
              & m1_yellow19(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_yellow19(X2,X0,X1)
               => r1_waybel_0(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_yellow19(X2,X0,X1)
             => r1_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',t9_yellow19)).

fof(f168,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f138])).

fof(f8443,plain,(
    u1_struct_0(sK0) = o_0_0_xboole_0 ),
    inference(unit_resulting_resolution,[],[f465,f467,f1764,f8442])).

fof(f8442,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | u1_struct_0(sK0) = o_0_0_xboole_0
      | r2_hidden(k2_waybel_0(sK0,sK1,X10),sK2)
      | ~ m1_subset_1(X10,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f2997,f1765])).

fof(f1765,plain,(
    ~ v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f909,f224])).

fof(f224,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',t7_boole)).

fof(f909,plain,(
    r2_hidden(sK8(sK0,sK1,sK2,sK7(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f173,f311,f465,f466,f390])).

fof(f390,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(X8,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ r1_orders_2(X1,X2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f389,f231])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f110])).

fof(f110,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',dt_k4_waybel_9)).

fof(f389,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(X8,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ r1_orders_2(X1,X2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f260,f232])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f260,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(X8,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ r1_orders_2(X1,X2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f259])).

fof(f259,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,u1_struct_0(X3))
      | ~ r1_orders_2(X1,X2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f189])).

fof(f189,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,u1_struct_0(X3))
      | ~ r1_orders_2(X1,X2,X8)
      | X7 != X8
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f147])).

fof(f147,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ( ( ! [X5] :
                              ( ~ r1_orders_2(X1,X2,X5)
                              | sK4(X1,X2,X3) != X5
                              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                          | ~ r2_hidden(sK4(X1,X2,X3),u1_struct_0(X3)) )
                        & ( ( r1_orders_2(X1,X2,sK5(X1,X2,X3))
                            & sK4(X1,X2,X3) = sK5(X1,X2,X3)
                            & m1_subset_1(sK5(X1,X2,X3),u1_struct_0(X1)) )
                          | r2_hidden(sK4(X1,X2,X3),u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X7] :
                            ( ( r2_hidden(X7,u1_struct_0(X3))
                              | ! [X8] :
                                  ( ~ r1_orders_2(X1,X2,X8)
                                  | X7 != X8
                                  | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
                            & ( ( r1_orders_2(X1,X2,sK6(X1,X2,X7))
                                & sK6(X1,X2,X7) = X7
                                & m1_subset_1(sK6(X1,X2,X7),u1_struct_0(X1)) )
                              | ~ r2_hidden(X7,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f143,f146,f145,f144])).

fof(f144,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_orders_2(X1,X2,X5)
                | X4 != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r2_hidden(X4,u1_struct_0(X3)) )
          & ( ? [X6] :
                ( r1_orders_2(X1,X2,X6)
                & X4 = X6
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | r2_hidden(X4,u1_struct_0(X3)) ) )
     => ( ( ! [X5] :
              ( ~ r1_orders_2(X1,X2,X5)
              | sK4(X1,X2,X3) != X5
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(sK4(X1,X2,X3),u1_struct_0(X3)) )
        & ( ? [X6] :
              ( r1_orders_2(X1,X2,X6)
              & sK4(X1,X2,X3) = X6
              & m1_subset_1(X6,u1_struct_0(X1)) )
          | r2_hidden(sK4(X1,X2,X3),u1_struct_0(X3)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f145,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r1_orders_2(X1,X2,X6)
          & X4 = X6
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X2,sK5(X1,X2,X3))
        & sK5(X1,X2,X3) = X4
        & m1_subset_1(sK5(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f146,plain,(
    ! [X7,X2,X1] :
      ( ? [X9] :
          ( r1_orders_2(X1,X2,X9)
          & X7 = X9
          & m1_subset_1(X9,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X2,sK6(X1,X2,X7))
        & sK6(X1,X2,X7) = X7
        & m1_subset_1(sK6(X1,X2,X7),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f143,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X6] :
                                ( r1_orders_2(X1,X2,X6)
                                & X4 = X6
                                & m1_subset_1(X6,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X7] :
                            ( ( r2_hidden(X7,u1_struct_0(X3))
                              | ! [X8] :
                                  ( ~ r1_orders_2(X1,X2,X8)
                                  | X7 != X8
                                  | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
                            & ( ? [X9] :
                                  ( r1_orders_2(X1,X2,X9)
                                  & X7 = X9
                                  & m1_subset_1(X9,u1_struct_0(X1)) )
                              | ~ r2_hidden(X7,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f142])).

fof(f142,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X5] :
                                ( r1_orders_2(X1,X2,X5)
                                & X4 = X5
                                & m1_subset_1(X5,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X4] :
                            ( ( r2_hidden(X4,u1_struct_0(X3))
                              | ! [X5] :
                                  ( ~ r1_orders_2(X1,X2,X5)
                                  | X4 != X5
                                  | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                            & ( ? [X5] :
                                  ( r1_orders_2(X1,X2,X5)
                                  & X4 = X5
                                  & m1_subset_1(X5,u1_struct_0(X1)) )
                              | ~ r2_hidden(X4,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f141])).

fof(f141,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X5] :
                                ( r1_orders_2(X1,X2,X5)
                                & X4 = X5
                                & m1_subset_1(X5,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X4] :
                            ( ( r2_hidden(X4,u1_struct_0(X3))
                              | ! [X5] :
                                  ( ~ r1_orders_2(X1,X2,X5)
                                  | X4 != X5
                                  | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                            & ( ? [X5] :
                                  ( r1_orders_2(X1,X2,X5)
                                  & X4 = X5
                                  & m1_subset_1(X5,u1_struct_0(X1)) )
                              | ~ r2_hidden(X4,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',d7_waybel_9)).

fof(f466,plain,(
    r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK8(sK0,sK1,sK2,sK7(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f173,f175,f311,f202])).

fof(f202,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X3,sK8(X0,X1,X2,X3))
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f156])).

fof(f156,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK8(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK8(X0,X1,X2,X3))
                      & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK9(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f153,f155,f154])).

fof(f154,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK8(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK8(X0,X1,X2,X3))
        & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f155,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK9(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f153,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f152])).

fof(f152,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',d11_waybel_0)).

fof(f175,plain,(
    ~ r1_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f138])).

fof(f311,plain,(
    m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f173,f174,f310])).

fof(f310,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_yellow19(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f196,f217])).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_yellow19(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_yellow19(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_yellow19(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow19(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',dt_m1_yellow19)).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_yellow19(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f151])).

fof(f151,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK7(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK7(X0,X1,X2)))) = X2
                    & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f149,f150])).

fof(f150,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK7(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK7(X0,X1,X2)))) = X2
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f149,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ? [X4] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f148])).

fof(f148,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ? [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                      & m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',d2_yellow19)).

fof(f174,plain,(
    m1_yellow19(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f138])).

fof(f173,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f138])).

fof(f170,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f138])).

fof(f2997,plain,(
    ! [X10] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X10),sK2)
      | u1_struct_0(sK0) = o_0_0_xboole_0
      | ~ m1_subset_1(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f2996,f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',t2_subset)).

fof(f2996,plain,(
    ! [X10] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X10),sK2)
      | u1_struct_0(sK0) = o_0_0_xboole_0
      | ~ r2_hidden(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f2995,f170])).

fof(f2995,plain,(
    ! [X10] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X10),sK2)
      | u1_struct_0(sK0) = o_0_0_xboole_0
      | ~ r2_hidden(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f2994,f172])).

fof(f172,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f138])).

fof(f2994,plain,(
    ! [X10] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X10),sK2)
      | u1_struct_0(sK0) = o_0_0_xboole_0
      | ~ r2_hidden(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f2993,f173])).

fof(f2993,plain,(
    ! [X10] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X10),sK2)
      | u1_struct_0(sK0) = o_0_0_xboole_0
      | ~ r2_hidden(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f2992,f311])).

fof(f2992,plain,(
    ! [X10] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X10),sK2)
      | u1_struct_0(sK0) = o_0_0_xboole_0
      | ~ r2_hidden(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f2991,f168])).

fof(f2991,plain,(
    ! [X10] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X10),sK2)
      | u1_struct_0(sK0) = o_0_0_xboole_0
      | ~ r2_hidden(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f2990,f169])).

fof(f2990,plain,(
    ! [X10] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X10),sK2)
      | u1_struct_0(sK0) = o_0_0_xboole_0
      | ~ r2_hidden(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f2989,f808])).

fof(f808,plain,(
    ~ v2_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f171,f172,f173,f647,f212])).

fof(f212,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | ~ v2_struct_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',dt_m2_yellow_6)).

fof(f647,plain,(
    m2_yellow_6(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2)),sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f171,f172,f173,f311,f319])).

fof(f319,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f316])).

fof(f316,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f229,f227])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2] :
      ( k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f104])).

fof(f104,plain,(
    ! [X0,X1,X2] :
      ( k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',redefinition_k5_waybel_9)).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
        & v6_waybel_0(k5_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f106])).

fof(f106,plain,(
    ! [X0,X1,X2] :
      ( ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
        & v6_waybel_0(k5_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
        & v6_waybel_0(k5_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',dt_k5_waybel_9)).

fof(f171,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f138])).

fof(f2989,plain,(
    ! [X10] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X10),sK2)
      | u1_struct_0(sK0) = o_0_0_xboole_0
      | ~ r2_hidden(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | v2_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f2988,f781])).

fof(f781,plain,(
    v1_funct_2(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))),u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f169,f473,f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',dt_u1_waybel_0)).

fof(f473,plain,(
    l1_waybel_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2)),sK0) ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f173,f311,f232])).

fof(f2988,plain,(
    ! [X10] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X10),sK2)
      | u1_struct_0(sK0) = o_0_0_xboole_0
      | ~ r2_hidden(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ v1_funct_2(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))),u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))),u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | v2_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f2976,f782])).

fof(f782,plain,(
    m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f169,f473,f221])).

fof(f221,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f2976,plain,(
    ! [X10] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X10),sK2)
      | u1_struct_0(sK0) = o_0_0_xboole_0
      | ~ r2_hidden(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))),u1_struct_0(sK0))))
      | ~ v1_funct_2(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))),u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))),u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | v2_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(superposition,[],[f1231,f384])).

fof(f384,plain,(
    k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2))),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2)))) = sK2 ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f173,f174,f383])).

fof(f383,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK7(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK7(X0,X1,X2)))) = X2
      | ~ m1_yellow19(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f197,f217])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK7(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK7(X0,X1,X2)))) = X2
      | ~ m1_yellow19(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f151])).

fof(f1231,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X3),k2_relset_1(X4,X5,u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | o_0_0_xboole_0 = X5
      | ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X4,X5)
      | ~ m1_subset_1(X3,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f1230,f232])).

fof(f1230,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X3),k2_relset_1(X4,X5,u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | o_0_0_xboole_0 = X5
      | ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X4,X5)
      | ~ m1_subset_1(X3,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f1222])).

fof(f1222,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X3),k2_relset_1(X4,X5,u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | o_0_0_xboole_0 = X5
      | ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X4,X5)
      | ~ m1_subset_1(X3,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f654,f255])).

fof(f255,plain,(
    ! [X4,X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X4) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f184])).

fof(f184,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
                     => ( X3 = X4
                       => k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',t16_waybel_9)).

fof(f654,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X2),k2_relset_1(X3,X4,u1_waybel_0(X0,X1)))
      | o_0_0_xboole_0 = X4
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(u1_waybel_0(X0,X1),X3,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f653,f219])).

fof(f219,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f653,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X2),k2_relset_1(X3,X4,u1_waybel_0(X0,X1)))
      | o_0_0_xboole_0 = X4
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(u1_waybel_0(X0,X1),X3,X4)
      | ~ v1_funct_1(u1_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(superposition,[],[f254,f333])).

fof(f333,plain,(
    ! [X4,X5,X3] :
      ( k2_waybel_0(X4,X3,X5) = k1_funct_1(u1_waybel_0(X4,X3),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f332,f219])).

fof(f332,plain,(
    ! [X4,X5,X3] :
      ( k2_waybel_0(X4,X3,X5) = k1_funct_1(u1_waybel_0(X4,X3),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | ~ v1_funct_1(u1_waybel_0(X4,X3))
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f331,f220])).

fof(f331,plain,(
    ! [X4,X5,X3] :
      ( k2_waybel_0(X4,X3,X5) = k1_funct_1(u1_waybel_0(X4,X3),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(u1_waybel_0(X4,X3),u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(u1_waybel_0(X4,X3))
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f330,f221])).

fof(f330,plain,(
    ! [X4,X5,X3] :
      ( k2_waybel_0(X4,X3,X5) = k1_funct_1(u1_waybel_0(X4,X3),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(u1_waybel_0(X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | ~ v1_funct_2(u1_waybel_0(X4,X3),u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(u1_waybel_0(X4,X3))
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,(
    ! [X4,X5,X3] :
      ( k2_waybel_0(X4,X3,X5) = k1_funct_1(u1_waybel_0(X4,X3),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(u1_waybel_0(X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | ~ v1_funct_2(u1_waybel_0(X4,X3),u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(u1_waybel_0(X4,X3))
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(superposition,[],[f185,f236])).

fof(f236,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f118,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f117])).

fof(f117,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',redefinition_k3_funct_2)).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',d8_waybel_0)).

fof(f254,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | o_0_0_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_unfolding,[],[f237,f177])).

fof(f177,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',d2_xboole_0)).

fof(f237,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f119])).

fof(f119,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',t6_funct_2)).

fof(f1764,plain,(
    m1_subset_1(sK8(sK0,sK1,sK2,sK7(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK7(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f909,f210])).

fof(f210,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t9_yellow19.p',t1_subset)).

fof(f467,plain,(
    ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK7(sK0,sK1,sK2))),sK2) ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f173,f175,f311,f203])).

fof(f203,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,sK8(X0,X1,X2,X3)),X2)
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f156])).

fof(f465,plain,(
    m1_subset_1(sK8(sK0,sK1,sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f173,f175,f311,f201])).

fof(f201,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f156])).
%------------------------------------------------------------------------------
