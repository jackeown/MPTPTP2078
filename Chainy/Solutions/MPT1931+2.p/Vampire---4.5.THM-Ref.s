%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1931+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:38 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 183 expanded)
%              Number of leaves         :   11 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  293 (1272 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6009,plain,(
    $false ),
    inference(resolution,[],[f5994,f4186])).

fof(f4186,plain,(
    ! [X0] : m1_subset_1(sK16(X0),X0) ),
    inference(cnf_transformation,[],[f4072])).

fof(f4072,plain,(
    ! [X0] : m1_subset_1(sK16(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f474,f4071])).

fof(f4071,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK16(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f474,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f5994,plain,(
    ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f5975,f4423])).

fof(f4423,plain,(
    ! [X2] :
      ( ~ r2_hidden(k2_waybel_0(sK1,sK2,sK3(sK1,sK2,u1_struct_0(sK1),X2)),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f4422,f4135])).

fof(f4135,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f4038])).

fof(f4038,plain,
    ( ~ r1_waybel_0(sK1,sK2,u1_struct_0(sK1))
    & l1_waybel_0(sK2,sK1)
    & v7_waybel_0(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f3907,f4037,f4036])).

fof(f4036,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK1,X1,u1_struct_0(sK1))
          & l1_waybel_0(X1,sK1)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f4037,plain,
    ( ? [X1] :
        ( ~ r1_waybel_0(sK1,X1,u1_struct_0(sK1))
        & l1_waybel_0(X1,sK1)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_waybel_0(sK1,sK2,u1_struct_0(sK1))
      & l1_waybel_0(sK2,sK1)
      & v7_waybel_0(sK2)
      & v4_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3907,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3906])).

fof(f3906,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3892])).

fof(f3892,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f3891])).

fof(f3891,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f4422,plain,(
    ! [X2] :
      ( ~ r2_hidden(k2_waybel_0(sK1,sK2,sK3(sK1,sK2,u1_struct_0(sK1),X2)),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f4421,f4136])).

fof(f4136,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f4038])).

fof(f4421,plain,(
    ! [X2] :
      ( ~ r2_hidden(k2_waybel_0(sK1,sK2,sK3(sK1,sK2,u1_struct_0(sK1),X2)),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f4420,f4137])).

fof(f4137,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f4038])).

fof(f4420,plain,(
    ! [X2] :
      ( ~ r2_hidden(k2_waybel_0(sK1,sK2,sK3(sK1,sK2,u1_struct_0(sK1),X2)),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | v2_struct_0(sK2)
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f4411,f4140])).

fof(f4140,plain,(
    l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f4038])).

fof(f4411,plain,(
    ! [X2] :
      ( ~ r2_hidden(k2_waybel_0(sK1,sK2,sK3(sK1,sK2,u1_struct_0(sK1),X2)),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ l1_waybel_0(sK2,sK1)
      | v2_struct_0(sK2)
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f4141,f4146])).

fof(f4146,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4043])).

fof(f4043,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK3(X0,X1,X2,X3))
                      & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK4(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f4040,f4042,f4041])).

fof(f4041,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK3(X0,X1,X2,X3))
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4042,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK4(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4040,plain,(
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
    inference(rectify,[],[f4039])).

fof(f4039,plain,(
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
    inference(nnf_transformation,[],[f3909])).

fof(f3909,plain,(
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
    inference(flattening,[],[f3908])).

fof(f3908,plain,(
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
    inference(ennf_transformation,[],[f3159])).

fof(f3159,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f4141,plain,(
    ~ r1_waybel_0(sK1,sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f4038])).

fof(f5975,plain,(
    ! [X0] :
      ( r2_hidden(k2_waybel_0(sK1,sK2,sK3(sK1,sK2,u1_struct_0(sK1),X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f4811,f4415])).

fof(f4415,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK1,sK2,u1_struct_0(sK1),X0),u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f4414,f4135])).

fof(f4414,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK1,sK2,u1_struct_0(sK1),X0),u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f4413,f4136])).

fof(f4413,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK1,sK2,u1_struct_0(sK1),X0),u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f4412,f4137])).

fof(f4412,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK1,sK2,u1_struct_0(sK1),X0),u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v2_struct_0(sK2)
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f4409,f4140])).

fof(f4409,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK1,sK2,u1_struct_0(sK1),X0),u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_waybel_0(sK2,sK1)
      | v2_struct_0(sK2)
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f4141,f4144])).

fof(f4144,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4043])).

fof(f4811,plain,(
    ! [X34] :
      ( ~ m1_subset_1(X34,u1_struct_0(sK2))
      | r2_hidden(k2_waybel_0(sK1,sK2,X34),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4808,f4340])).

fof(f4340,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_subsumption,[],[f4136,f4335])).

fof(f4335,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(resolution,[],[f4135,f4160])).

fof(f4160,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3921])).

fof(f3921,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3920])).

fof(f3920,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f4808,plain,(
    ! [X34] :
      ( ~ m1_subset_1(X34,u1_struct_0(sK2))
      | r2_hidden(k2_waybel_0(sK1,sK2,X34),u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f4400,f4265])).

fof(f4265,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f4107])).

fof(f4107,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f4012])).

fof(f4012,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f4400,plain,(
    ! [X8] :
      ( m1_subset_1(k2_waybel_0(sK1,sK2,X8),u1_struct_0(sK1))
      | ~ m1_subset_1(X8,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f4399,f4135])).

fof(f4399,plain,(
    ! [X8] :
      ( m1_subset_1(k2_waybel_0(sK1,sK2,X8),u1_struct_0(sK1))
      | ~ m1_subset_1(X8,u1_struct_0(sK2))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f4398,f4136])).

fof(f4398,plain,(
    ! [X8] :
      ( m1_subset_1(k2_waybel_0(sK1,sK2,X8),u1_struct_0(sK1))
      | ~ m1_subset_1(X8,u1_struct_0(sK2))
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f4396,f4137])).

fof(f4396,plain,(
    ! [X8] :
      ( m1_subset_1(k2_waybel_0(sK1,sK2,X8),u1_struct_0(sK1))
      | ~ m1_subset_1(X8,u1_struct_0(sK2))
      | v2_struct_0(sK2)
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f4140,f4184])).

fof(f4184,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3943])).

fof(f3943,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3942])).

fof(f3942,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3191])).

fof(f3191,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).
%------------------------------------------------------------------------------
