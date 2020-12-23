%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1971+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:57 EST 2020

% Result     : Theorem 23.05s
% Output     : CNFRefutation 23.05s
% Verified   : 
% Statistics : Number of formulae       :  485 (202535 expanded)
%              Number of clauses        :  376 (44204 expanded)
%              Number of leaves         :   26 (46513 expanded)
%              Depth                    :   54
%              Number of atoms          : 2725 (3437946 expanded)
%              Number of equality atoms :  460 (26830 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   52 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f60])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v2_waybel_0(X1,k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v13_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v13_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v13_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v13_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f62])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v13_waybel_0(X1,k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | r2_hidden(X2,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f50])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X2,X1)
          & r2_hidden(k12_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & ~ r2_hidden(X2,X1)
        & r2_hidden(k12_lattice3(X0,X2,sK1(X0,X1)),X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X2,X1)
              & r2_hidden(k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(sK0(X0,X1),X1)
            & r2_hidden(k12_lattice3(X0,sK0(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK1(X0,X1),X1)
                & ~ r2_hidden(sK0(X0,X1),X1)
                & r2_hidden(k12_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_7(X1,X0)
            | ~ v12_waybel_0(X1,X0)
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f65,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_7(X1,X0)
            | ~ v12_waybel_0(X1,X0)
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f64])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_7(X1,X0)
            | ~ v12_waybel_0(X1,X0)
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
     => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          | ~ v2_waybel_7(sK5,k7_lattice3(X0))
          | ~ v13_waybel_0(sK5,k7_lattice3(X0))
          | ~ v2_waybel_0(sK5,k7_lattice3(X0))
          | v1_xboole_0(sK5)
          | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_waybel_7(sK5,X0)
          | ~ v12_waybel_0(sK5,X0)
          | ~ v1_waybel_0(sK5,X0)
          | v1_xboole_0(sK5) )
        & ( ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(sK5,k7_lattice3(X0))
            & v13_waybel_0(sK5,k7_lattice3(X0))
            & v2_waybel_0(sK5,k7_lattice3(X0))
            & ~ v1_xboole_0(sK5) )
          | ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(sK5,X0)
            & v12_waybel_0(sK5,X0)
            & v1_waybel_0(sK5,X0)
            & ~ v1_xboole_0(sK5) ) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              | ~ v2_waybel_7(X1,k7_lattice3(X0))
              | ~ v13_waybel_0(X1,k7_lattice3(X0))
              | ~ v2_waybel_0(X1,k7_lattice3(X0))
              | v1_xboole_0(X1)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_waybel_7(X1,X0)
              | ~ v12_waybel_0(X1,X0)
              | ~ v1_waybel_0(X1,X0)
              | v1_xboole_0(X1) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
                & v2_waybel_7(X1,k7_lattice3(X0))
                & v13_waybel_0(X1,k7_lattice3(X0))
                & v2_waybel_0(X1,k7_lattice3(X0))
                & ~ v1_xboole_0(X1) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X1,X0)
                & v12_waybel_0(X1,X0)
                & v1_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) ) ) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
            | ~ v2_waybel_7(X1,k7_lattice3(sK4))
            | ~ v13_waybel_0(X1,k7_lattice3(sK4))
            | ~ v2_waybel_0(X1,k7_lattice3(sK4))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
            | ~ v1_waybel_7(X1,sK4)
            | ~ v12_waybel_0(X1,sK4)
            | ~ v1_waybel_0(X1,sK4)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
              & v2_waybel_7(X1,k7_lattice3(sK4))
              & v13_waybel_0(X1,k7_lattice3(sK4))
              & v2_waybel_0(X1,k7_lattice3(sK4))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
              & v1_waybel_7(X1,sK4)
              & v12_waybel_0(X1,sK4)
              & v1_waybel_0(X1,sK4)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(sK4)
      & v2_lattice3(sK4)
      & v1_lattice3(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
      | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
      | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
      | ~ v2_waybel_0(sK5,k7_lattice3(sK4))
      | v1_xboole_0(sK5)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v1_waybel_7(sK5,sK4)
      | ~ v12_waybel_0(sK5,sK4)
      | ~ v1_waybel_0(sK5,sK4)
      | v1_xboole_0(sK5) )
    & ( ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
        & v2_waybel_7(sK5,k7_lattice3(sK4))
        & v13_waybel_0(sK5,k7_lattice3(sK4))
        & v2_waybel_0(sK5,k7_lattice3(sK4))
        & ~ v1_xboole_0(sK5) )
      | ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
        & v1_waybel_7(sK5,sK4)
        & v12_waybel_0(sK5,sK4)
        & v1_waybel_0(sK5,sK4)
        & ~ v1_xboole_0(sK5) ) )
    & l1_orders_2(sK4)
    & v2_lattice3(sK4)
    & v1_lattice3(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f65,f67,f66])).

fof(f111,plain,(
    v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f107,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f108,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f109,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f112,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f133,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f113,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f126,plain,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f136,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f121,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f135,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | v12_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f137,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f68])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v13_waybel_0(X1,k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f125,plain,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | v12_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f127,plain,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f68])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k8_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f119,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | v1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f122,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f68])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | r2_hidden(X2,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f55])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X2,X1)
          & r2_hidden(k13_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & ~ r2_hidden(X2,X1)
        & r2_hidden(k13_lattice3(X0,X2,sK3(X0,X1)),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X2,X1)
              & r2_hidden(k13_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(sK2(X0,X1),X1)
            & r2_hidden(k13_lattice3(X0,sK2(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & ~ r2_hidden(sK2(X0,X1),X1)
                & r2_hidden(k13_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f56,f58,f57])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(flattening,[],[f39])).

fof(f95,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f85,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f89,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f91,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0] :
      ( ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f93,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f138,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v1_xboole_0(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ v1_waybel_0(sK5,sK4)
    | v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
         => k9_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k9_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k7_lattice3(X0)))
             => k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f131,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | r2_hidden(k13_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f130,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | v12_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f70,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v1_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f129,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | v1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f132,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f68])).

fof(f76,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | r2_hidden(k12_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_30,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | v1_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_34,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_5,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_65,negated_conjecture,
    ( v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_849,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_65])).

cnf(c_850,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_849])).

cnf(c_69,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_68,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_67,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_64,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_854,plain,
    ( v1_xboole_0(X0)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_850,c_69,c_68,c_67,c_64])).

cnf(c_855,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_854])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_63,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_411,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_43,c_63])).

cnf(c_1139,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_855,c_411])).

cnf(c_1140,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_1139])).

cnf(c_2753,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_1140])).

cnf(c_2754,plain,
    ( ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2753])).

cnf(c_50,negated_conjecture,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_2756,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_0(sK5,sK4)
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2754,c_64,c_50,c_40])).

cnf(c_2757,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_2756])).

cnf(c_3733,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_2757])).

cnf(c_3734,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3733])).

cnf(c_55,negated_conjecture,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_35,plain,
    ( ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_41,negated_conjecture,
    ( v12_waybel_0(sK5,sK4)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_2943,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_41])).

cnf(c_2944,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2943])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_2946,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2944,c_64,c_39])).

cnf(c_3736,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3734,c_64,c_55,c_39,c_2944])).

cnf(c_3737,plain,
    ( m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3736])).

cnf(c_7484,plain,
    ( m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4) ),
    inference(subtyping,[status(esa)],[c_3737])).

cnf(c_8572,plain,
    ( m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_waybel_7(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7484])).

cnf(c_7541,plain,
    ( X0_60 != X1_60
    | k7_lattice3(X0_60) = k7_lattice3(X1_60) ),
    theory(equality)).

cnf(c_7561,plain,
    ( k7_lattice3(sK4) = k7_lattice3(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_7541])).

cnf(c_7518,plain,
    ( X0_60 = X0_60 ),
    theory(equality)).

cnf(c_7564,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_7518])).

cnf(c_33,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_36,plain,
    ( v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_51,negated_conjecture,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | v12_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_2896,plain,
    ( v13_waybel_0(X0,k7_lattice3(X1))
    | v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_51])).

cnf(c_2897,plain,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2896])).

cnf(c_49,negated_conjecture,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_2899,plain,
    ( v13_waybel_0(sK5,k7_lattice3(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2897,c_64,c_49])).

cnf(c_3042,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ l1_orders_2(X1)
    | k7_lattice3(X1) != k7_lattice3(sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_2899])).

cnf(c_3043,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
    | ~ l1_orders_2(X0)
    | k7_lattice3(X0) != k7_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_3042])).

cnf(c_7489,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_60)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_60))))
    | ~ l1_orders_2(X0_60)
    | k7_lattice3(X0_60) != k7_lattice3(sK4) ),
    inference(subtyping,[status(esa)],[c_3043])).

cnf(c_7607,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4)
    | k7_lattice3(sK4) != k7_lattice3(sK4) ),
    inference(instantiation,[status(thm)],[c_7489])).

cnf(c_7742,plain,
    ( m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | v1_waybel_7(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7484,c_64,c_39,c_2944,c_3737,c_7561,c_7564,c_7607])).

cnf(c_7744,plain,
    ( m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | v1_waybel_7(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7742])).

cnf(c_10437,plain,
    ( m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | v1_waybel_7(sK5,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8572,c_7744])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | k8_lattice3(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_7509,plain,
    ( ~ m1_subset_1(X0_59,u1_struct_0(X0_60))
    | ~ l1_orders_2(X0_60)
    | k8_lattice3(X0_60,X0_59) = X0_59 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_8547,plain,
    ( k8_lattice3(X0_60,X0_59) = X0_59
    | m1_subset_1(X0_59,u1_struct_0(X0_60)) != iProver_top
    | l1_orders_2(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7509])).

cnf(c_10443,plain,
    ( k8_lattice3(sK4,sK0(sK4,sK5)) = sK0(sK4,sK5)
    | v1_waybel_7(sK5,sK4) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10437,c_8547])).

cnf(c_75,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_10571,plain,
    ( v1_waybel_7(sK5,sK4) = iProver_top
    | k8_lattice3(sK4,sK0(sK4,sK5)) = sK0(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10443,c_75])).

cnf(c_10572,plain,
    ( k8_lattice3(sK4,sK0(sK4,sK5)) = sK0(sK4,sK5)
    | v1_waybel_7(sK5,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_10571])).

cnf(c_4,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_879,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_65])).

cnf(c_880,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_879])).

cnf(c_884,plain,
    ( v1_xboole_0(X0)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_880,c_69,c_68,c_67,c_64])).

cnf(c_885,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_884])).

cnf(c_1120,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_885,c_411])).

cnf(c_1121,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_1120])).

cnf(c_2773,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_1121])).

cnf(c_2774,plain,
    ( ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2773])).

cnf(c_2776,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_0(sK5,sK4)
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2774,c_64,c_50,c_40])).

cnf(c_2777,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_2776])).

cnf(c_3716,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_2777])).

cnf(c_3717,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3716])).

cnf(c_3719,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3717,c_64,c_55,c_39,c_2944])).

cnf(c_3720,plain,
    ( m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3719])).

cnf(c_7485,plain,
    ( m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4) ),
    inference(subtyping,[status(esa)],[c_3720])).

cnf(c_8571,plain,
    ( m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_waybel_7(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7485])).

cnf(c_7737,plain,
    ( m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | v1_waybel_7(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7485,c_64,c_39,c_2944,c_3720,c_7561,c_7564,c_7607])).

cnf(c_7739,plain,
    ( m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | v1_waybel_7(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7737])).

cnf(c_10424,plain,
    ( m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | v1_waybel_7(sK5,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8571,c_7739])).

cnf(c_10430,plain,
    ( k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5)
    | v1_waybel_7(sK5,sK4) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10424,c_8547])).

cnf(c_10563,plain,
    ( v1_waybel_7(sK5,sK4) = iProver_top
    | k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10430,c_75])).

cnf(c_10564,plain,
    ( k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5)
    | v1_waybel_7(sK5,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_10563])).

cnf(c_32,plain,
    ( v2_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_57,negated_conjecture,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | v1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3783,plain,
    ( v2_waybel_0(X0,k7_lattice3(X1))
    | v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_57])).

cnf(c_3784,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3783])).

cnf(c_54,negated_conjecture,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_3786,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3784,c_64,c_54])).

cnf(c_10,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1275,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_411])).

cnf(c_1276,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | m1_subset_1(sK3(X0,sK5),u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_1275])).

cnf(c_25,plain,
    ( v1_lattice3(k7_lattice3(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_775,plain,
    ( v1_lattice3(k7_lattice3(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_65])).

cnf(c_776,plain,
    ( v1_lattice3(k7_lattice3(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_778,plain,
    ( v1_lattice3(k7_lattice3(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_776,c_64])).

cnf(c_1765,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | m1_subset_1(sK3(X0,sK5),u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k7_lattice3(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1276,c_778])).

cnf(c_1766,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(unflattening,[status(thm)],[c_1765])).

cnf(c_3009,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2899,c_1766])).

cnf(c_3024,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2946,c_3009])).

cnf(c_3832,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3786,c_3024])).

cnf(c_7481,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(subtyping,[status(esa)],[c_3832])).

cnf(c_8576,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7481])).

cnf(c_70,plain,
    ( v3_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_71,plain,
    ( v4_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_72,plain,
    ( v5_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_2948,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2946])).

cnf(c_3016,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4)) != iProver_top
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) != iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3009])).

cnf(c_3788,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3786])).

cnf(c_15,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_7507,plain,
    ( ~ l1_orders_2(X0_60)
    | l1_orders_2(k7_lattice3(X0_60)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_7572,plain,
    ( l1_orders_2(X0_60) != iProver_top
    | l1_orders_2(k7_lattice3(X0_60)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7507])).

cnf(c_7574,plain,
    ( l1_orders_2(k7_lattice3(sK4)) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7572])).

cnf(c_19,plain,
    ( ~ v3_orders_2(X0)
    | v3_orders_2(k7_lattice3(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_7504,plain,
    ( ~ v3_orders_2(X0_60)
    | v3_orders_2(k7_lattice3(X0_60))
    | ~ l1_orders_2(X0_60) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_7581,plain,
    ( v3_orders_2(X0_60) != iProver_top
    | v3_orders_2(k7_lattice3(X0_60)) = iProver_top
    | l1_orders_2(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7504])).

cnf(c_7583,plain,
    ( v3_orders_2(k7_lattice3(sK4)) = iProver_top
    | v3_orders_2(sK4) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7581])).

cnf(c_21,plain,
    ( ~ v4_orders_2(X0)
    | v4_orders_2(k7_lattice3(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_7503,plain,
    ( ~ v4_orders_2(X0_60)
    | v4_orders_2(k7_lattice3(X0_60))
    | ~ l1_orders_2(X0_60) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_7584,plain,
    ( v4_orders_2(X0_60) != iProver_top
    | v4_orders_2(k7_lattice3(X0_60)) = iProver_top
    | l1_orders_2(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7503])).

cnf(c_7586,plain,
    ( v4_orders_2(k7_lattice3(sK4)) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7584])).

cnf(c_23,plain,
    ( ~ v5_orders_2(X0)
    | v5_orders_2(k7_lattice3(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_7502,plain,
    ( ~ v5_orders_2(X0_60)
    | v5_orders_2(k7_lattice3(X0_60))
    | ~ l1_orders_2(X0_60) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_7587,plain,
    ( v5_orders_2(X0_60) != iProver_top
    | v5_orders_2(k7_lattice3(X0_60)) = iProver_top
    | l1_orders_2(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7502])).

cnf(c_7589,plain,
    ( v5_orders_2(k7_lattice3(sK4)) = iProver_top
    | v5_orders_2(sK4) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7587])).

cnf(c_9488,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8576,c_70,c_71,c_72,c_75,c_2948,c_3016,c_3788,c_7574,c_7583,c_7586,c_7589])).

cnf(c_9496,plain,
    ( k8_lattice3(k7_lattice3(sK4),sK3(k7_lattice3(sK4),sK5)) = sK3(k7_lattice3(sK4),sK5)
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9488,c_8547])).

cnf(c_10628,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | k8_lattice3(k7_lattice3(sK4),sK3(k7_lattice3(sK4),sK5)) = sK3(k7_lattice3(sK4),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9496,c_75,c_7574])).

cnf(c_10629,plain,
    ( k8_lattice3(k7_lattice3(sK4),sK3(k7_lattice3(sK4),sK5)) = sK3(k7_lattice3(sK4),sK5)
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10628])).

cnf(c_38,negated_conjecture,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4)
    | v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_420,plain,
    ( ~ v1_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v12_waybel_0(sK5,sK4)
    | ~ v1_waybel_0(sK5,sK4)
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_0(sK5,k7_lattice3(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_38,c_63])).

cnf(c_421,negated_conjecture,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_420])).

cnf(c_2853,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_421])).

cnf(c_2854,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2853])).

cnf(c_2856,plain,
    ( ~ v1_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_0(sK5,k7_lattice3(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2854,c_64])).

cnf(c_2857,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_2856])).

cnf(c_2907,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2899,c_2857])).

cnf(c_2954,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2946,c_2907])).

cnf(c_3645,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_2954])).

cnf(c_3646,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3645])).

cnf(c_3648,plain,
    ( ~ v1_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3646,c_64,c_39,c_2944])).

cnf(c_3649,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3648])).

cnf(c_3793,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3786,c_3649])).

cnf(c_7482,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(subtyping,[status(esa)],[c_3793])).

cnf(c_8575,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_waybel_7(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7482])).

cnf(c_7753,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7482,c_64,c_39,c_2944,c_3793,c_7561,c_7564,c_7607])).

cnf(c_7755,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | v1_waybel_7(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7753])).

cnf(c_9090,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | v1_waybel_7(sK5,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8575,c_7755])).

cnf(c_10633,plain,
    ( k8_lattice3(k7_lattice3(sK4),sK3(k7_lattice3(sK4),sK5)) = sK3(k7_lattice3(sK4),sK5)
    | v1_waybel_7(sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10629,c_9090])).

cnf(c_10679,plain,
    ( k8_lattice3(k7_lattice3(sK4),sK3(k7_lattice3(sK4),sK5)) = sK3(k7_lattice3(sK4),sK5)
    | k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_10564,c_10633])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k8_lattice3(X1,X0),u1_struct_0(k7_lattice3(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_7506,plain,
    ( ~ m1_subset_1(X0_59,u1_struct_0(X0_60))
    | m1_subset_1(k8_lattice3(X0_60,X0_59),u1_struct_0(k7_lattice3(X0_60)))
    | ~ l1_orders_2(X0_60) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_8550,plain,
    ( m1_subset_1(X0_59,u1_struct_0(X0_60)) != iProver_top
    | m1_subset_1(k8_lattice3(X0_60,X0_59),u1_struct_0(k7_lattice3(X0_60))) = iProver_top
    | l1_orders_2(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7506])).

cnf(c_36336,plain,
    ( k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5)
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(k7_lattice3(sK4)))) = iProver_top
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10679,c_8550])).

cnf(c_4533,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(resolution,[status(thm)],[c_3832,c_3793])).

cnf(c_4534,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_waybel_7(sK5,sK4) != iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4533])).

cnf(c_7606,plain,
    ( k7_lattice3(X0_60) != k7_lattice3(sK4)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_60))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_60)))) != iProver_top
    | l1_orders_2(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7489])).

cnf(c_7608,plain,
    ( k7_lattice3(sK4) != k7_lattice3(sK4)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7606])).

cnf(c_36475,plain,
    ( k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5)
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(k7_lattice3(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36336,c_70,c_71,c_72,c_75,c_2948,c_4534,c_7561,c_7564,c_7574,c_7583,c_7586,c_7589,c_7608,c_10564])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(X1)))
    | ~ l1_orders_2(X1)
    | k9_lattice3(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_7508,plain,
    ( ~ m1_subset_1(X0_59,u1_struct_0(k7_lattice3(X0_60)))
    | ~ l1_orders_2(X0_60)
    | k9_lattice3(X0_60,X0_59) = X0_59 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_8548,plain,
    ( k9_lattice3(X0_60,X0_59) = X0_59
    | m1_subset_1(X0_59,u1_struct_0(k7_lattice3(X0_60))) != iProver_top
    | l1_orders_2(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7508])).

cnf(c_36519,plain,
    ( k9_lattice3(k7_lattice3(sK4),sK3(k7_lattice3(sK4),sK5)) = sK3(k7_lattice3(sK4),sK5)
    | k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5)
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_36475,c_8548])).

cnf(c_36690,plain,
    ( k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5)
    | k9_lattice3(k7_lattice3(sK4),sK3(k7_lattice3(sK4),sK5)) = sK3(k7_lattice3(sK4),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36519,c_75,c_7574])).

cnf(c_36691,plain,
    ( k9_lattice3(k7_lattice3(sK4),sK3(k7_lattice3(sK4),sK5)) = sK3(k7_lattice3(sK4),sK5)
    | k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_36690])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(X1)))
    | m1_subset_1(k9_lattice3(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_7505,plain,
    ( ~ m1_subset_1(X0_59,u1_struct_0(k7_lattice3(X0_60)))
    | m1_subset_1(k9_lattice3(X0_60,X0_59),u1_struct_0(X0_60))
    | ~ l1_orders_2(X0_60) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_8551,plain,
    ( m1_subset_1(X0_59,u1_struct_0(k7_lattice3(X0_60))) != iProver_top
    | m1_subset_1(k9_lattice3(X0_60,X0_59),u1_struct_0(X0_60)) = iProver_top
    | l1_orders_2(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7505])).

cnf(c_36692,plain,
    ( k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5)
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(k7_lattice3(sK4)))) != iProver_top
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_36691,c_8551])).

cnf(c_7573,plain,
    ( l1_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_7507])).

cnf(c_7582,plain,
    ( v3_orders_2(k7_lattice3(sK4))
    | ~ v3_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_7504])).

cnf(c_7585,plain,
    ( v4_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_7503])).

cnf(c_7588,plain,
    ( v5_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_7502])).

cnf(c_7758,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7481,c_69,c_68,c_67,c_64,c_54,c_49,c_39,c_1766,c_2897,c_2944,c_3784,c_7573,c_7582,c_7585,c_7588])).

cnf(c_7888,plain,
    ( ~ v1_waybel_7(sK5,sK4)
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4)) ),
    inference(prop_impl,[status(thm)],[c_64,c_54,c_39,c_2944,c_3649,c_3784,c_7561,c_7564,c_7607])).

cnf(c_7889,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_7888])).

cnf(c_7999,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(bin_hyper_res,[status(thm)],[c_7758,c_7889])).

cnf(c_8061,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | v1_waybel_7(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7999])).

cnf(c_36828,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36692,c_75,c_8061,c_10430])).

cnf(c_36829,plain,
    ( k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5)
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_36828])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,k9_lattice3(X1,X0),k9_lattice3(X1,X2)) = k13_lattice3(k7_lattice3(X1),X0,X2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_786,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,k9_lattice3(X1,X0),k9_lattice3(X1,X2)) = k13_lattice3(k7_lattice3(X1),X0,X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_65])).

cnf(c_787,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK4)))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | k12_lattice3(sK4,k9_lattice3(sK4,X1),k9_lattice3(sK4,X0)) = k13_lattice3(k7_lattice3(sK4),X1,X0) ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_791,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK4)))
    | k12_lattice3(sK4,k9_lattice3(sK4,X1),k9_lattice3(sK4,X0)) = k13_lattice3(k7_lattice3(sK4),X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_787,c_69,c_68,c_67,c_64])).

cnf(c_7493,plain,
    ( ~ m1_subset_1(X0_59,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1_59,u1_struct_0(k7_lattice3(sK4)))
    | k12_lattice3(sK4,k9_lattice3(sK4,X1_59),k9_lattice3(sK4,X0_59)) = k13_lattice3(k7_lattice3(sK4),X1_59,X0_59) ),
    inference(subtyping,[status(esa)],[c_791])).

cnf(c_8563,plain,
    ( k12_lattice3(sK4,k9_lattice3(sK4,X0_59),k9_lattice3(sK4,X1_59)) = k13_lattice3(k7_lattice3(sK4),X0_59,X1_59)
    | m1_subset_1(X0_59,u1_struct_0(k7_lattice3(sK4))) != iProver_top
    | m1_subset_1(X1_59,u1_struct_0(k7_lattice3(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7493])).

cnf(c_36850,plain,
    ( k12_lattice3(sK4,k9_lattice3(sK4,X0_59),k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))) = k13_lattice3(k7_lattice3(sK4),X0_59,sK3(k7_lattice3(sK4),sK5))
    | k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5)
    | m1_subset_1(X0_59,u1_struct_0(k7_lattice3(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_36829,c_8563])).

cnf(c_45,negated_conjecture,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_94,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | v1_waybel_7(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_11,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1239,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_411])).

cnf(c_1240,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | m1_subset_1(sK2(X0,sK5),u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_1239])).

cnf(c_1796,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | m1_subset_1(sK2(X0,sK5),u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k7_lattice3(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1240,c_778])).

cnf(c_1797,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(unflattening,[status(thm)],[c_1796])).

cnf(c_3010,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2899,c_1797])).

cnf(c_3015,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4)) != iProver_top
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) != iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3010])).

cnf(c_9,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k13_lattice3(X1,sK2(X1,X0),sK3(X1,X0)),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1311,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k13_lattice3(X1,sK2(X1,X0),sK3(X1,X0)),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_411])).

cnf(c_1312,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(k13_lattice3(X0,sK2(X0,sK5),sK3(X0,sK5)),sK5)
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_1311])).

cnf(c_1734,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(k13_lattice3(X0,sK2(X0,sK5),sK3(X0,sK5)),sK5)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k7_lattice3(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1312,c_778])).

cnf(c_1735,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | r2_hidden(k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5)),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(unflattening,[status(thm)],[c_1734])).

cnf(c_3008,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | r2_hidden(k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5)),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2899,c_1735])).

cnf(c_3017,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4)) != iProver_top
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) != iProver_top
    | r2_hidden(k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5)),sK5) = iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3008])).

cnf(c_8,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK2(X1,X0),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1347,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK2(X1,X0),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_411])).

cnf(c_1348,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(sK2(X0,sK5),sK5)
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_1347])).

cnf(c_1703,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(sK2(X0,sK5),sK5)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k7_lattice3(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1348,c_778])).

cnf(c_1704,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ r2_hidden(sK2(k7_lattice3(sK4),sK5),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(unflattening,[status(thm)],[c_1703])).

cnf(c_3007,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ r2_hidden(sK2(k7_lattice3(sK4),sK5),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2899,c_1704])).

cnf(c_3018,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4)) != iProver_top
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) != iProver_top
    | r2_hidden(sK2(k7_lattice3(sK4),sK5),sK5) != iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3007])).

cnf(c_7,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK3(X1,X0),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1383,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK3(X1,X0),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_411])).

cnf(c_1384,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(sK3(X0,sK5),sK5)
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_1383])).

cnf(c_1672,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(sK3(X0,sK5),sK5)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k7_lattice3(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1384,c_778])).

cnf(c_1673,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ r2_hidden(sK3(k7_lattice3(sK4),sK5),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(unflattening,[status(thm)],[c_1672])).

cnf(c_3006,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ r2_hidden(sK3(k7_lattice3(sK4),sK5),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2899,c_1673])).

cnf(c_3019,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4)) != iProver_top
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) != iProver_top
    | r2_hidden(sK3(k7_lattice3(sK4),sK5),sK5) != iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3006])).

cnf(c_4052,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_3720,c_3793])).

cnf(c_4053,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4052])).

cnf(c_7517,plain,
    ( X0_59 = X0_59 ),
    theory(equality)).

cnf(c_7563,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_7517])).

cnf(c_9372,plain,
    ( sK3(k7_lattice3(sK4),sK5) = sK3(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_7517])).

cnf(c_9375,plain,
    ( sK2(k7_lattice3(sK4),sK5) = sK2(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_7517])).

cnf(c_9494,plain,
    ( k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5)) = sK3(k7_lattice3(sK4),sK5)
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9488,c_8548])).

cnf(c_3023,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2946,c_3010])).

cnf(c_3833,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3786,c_3023])).

cnf(c_7480,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(subtyping,[status(esa)],[c_3833])).

cnf(c_8577,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7480])).

cnf(c_9572,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8577,c_70,c_71,c_72,c_75,c_2948,c_3015,c_3788,c_7574,c_7583,c_7586,c_7589])).

cnf(c_9493,plain,
    ( k12_lattice3(sK4,k9_lattice3(sK4,X0_59),k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))) = k13_lattice3(k7_lattice3(sK4),X0_59,sK3(k7_lattice3(sK4),sK5))
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(X0_59,u1_struct_0(k7_lattice3(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9488,c_8563])).

cnf(c_9576,plain,
    ( k12_lattice3(sK4,k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))) = k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5))
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9572,c_9493])).

cnf(c_9579,plain,
    ( k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)) = sK2(k7_lattice3(sK4),sK5)
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9572,c_8548])).

cnf(c_7528,plain,
    ( ~ r2_hidden(X0_59,X1_59)
    | r2_hidden(X2_59,X3_59)
    | X2_59 != X0_59
    | X3_59 != X1_59 ),
    theory(equality)).

cnf(c_8761,plain,
    ( ~ r2_hidden(X0_59,X1_59)
    | r2_hidden(X2_59,sK5)
    | X2_59 != X0_59
    | sK5 != X1_59 ),
    inference(instantiation,[status(thm)],[c_7528])).

cnf(c_9080,plain,
    ( r2_hidden(X0_59,sK5)
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5)),sK5)
    | X0_59 != k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_8761])).

cnf(c_9660,plain,
    ( ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5)),sK5)
    | r2_hidden(k12_lattice3(sK4,k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))),sK5)
    | k12_lattice3(sK4,k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))) != k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_9080])).

cnf(c_9661,plain,
    ( k12_lattice3(sK4,k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))) != k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5))
    | sK5 != sK5
    | r2_hidden(k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5)),sK5) != iProver_top
    | r2_hidden(k12_lattice3(sK4,k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9660])).

cnf(c_9424,plain,
    ( ~ m1_subset_1(X0_59,u1_struct_0(k7_lattice3(sK4)))
    | m1_subset_1(k9_lattice3(sK4,X0_59),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_7505])).

cnf(c_10317,plain,
    ( m1_subset_1(k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_9424])).

cnf(c_10318,plain,
    ( m1_subset_1(k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10317])).

cnf(c_10320,plain,
    ( m1_subset_1(k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_9424])).

cnf(c_10321,plain,
    ( m1_subset_1(k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10320])).

cnf(c_7520,plain,
    ( X0_59 != X1_59
    | X2_59 != X1_59
    | X2_59 = X0_59 ),
    theory(equality)).

cnf(c_8962,plain,
    ( X0_59 != X1_59
    | sK3(k7_lattice3(sK4),sK5) != X1_59
    | sK3(k7_lattice3(sK4),sK5) = X0_59 ),
    inference(instantiation,[status(thm)],[c_7520])).

cnf(c_9428,plain,
    ( X0_59 != sK3(k7_lattice3(sK4),sK5)
    | sK3(k7_lattice3(sK4),sK5) = X0_59
    | sK3(k7_lattice3(sK4),sK5) != sK3(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_8962])).

cnf(c_10329,plain,
    ( k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5)) != sK3(k7_lattice3(sK4),sK5)
    | sK3(k7_lattice3(sK4),sK5) = k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5))
    | sK3(k7_lattice3(sK4),sK5) != sK3(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_9428])).

cnf(c_10330,plain,
    ( k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5)) != sK3(k7_lattice3(sK4),sK5)
    | sK3(k7_lattice3(sK4),sK5) = k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))
    | sK3(k7_lattice3(sK4),sK5) != sK3(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_10329])).

cnf(c_8971,plain,
    ( X0_59 != X1_59
    | sK2(k7_lattice3(sK4),sK5) != X1_59
    | sK2(k7_lattice3(sK4),sK5) = X0_59 ),
    inference(instantiation,[status(thm)],[c_7520])).

cnf(c_9433,plain,
    ( X0_59 != sK2(k7_lattice3(sK4),sK5)
    | sK2(k7_lattice3(sK4),sK5) = X0_59
    | sK2(k7_lattice3(sK4),sK5) != sK2(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_8971])).

cnf(c_10339,plain,
    ( k9_lattice3(X0_60,sK2(k7_lattice3(sK4),sK5)) != sK2(k7_lattice3(sK4),sK5)
    | sK2(k7_lattice3(sK4),sK5) = k9_lattice3(X0_60,sK2(k7_lattice3(sK4),sK5))
    | sK2(k7_lattice3(sK4),sK5) != sK2(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_9433])).

cnf(c_10340,plain,
    ( k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)) != sK2(k7_lattice3(sK4),sK5)
    | sK2(k7_lattice3(sK4),sK5) = k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5))
    | sK2(k7_lattice3(sK4),sK5) != sK2(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_10339])).

cnf(c_8717,plain,
    ( ~ r2_hidden(X0_59,X1_59)
    | r2_hidden(sK3(k7_lattice3(sK4),sK5),sK5)
    | sK3(k7_lattice3(sK4),sK5) != X0_59
    | sK5 != X1_59 ),
    inference(instantiation,[status(thm)],[c_7528])).

cnf(c_13362,plain,
    ( ~ r2_hidden(k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5)),X0_59)
    | r2_hidden(sK3(k7_lattice3(sK4),sK5),sK5)
    | sK3(k7_lattice3(sK4),sK5) != k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5))
    | sK5 != X0_59 ),
    inference(instantiation,[status(thm)],[c_8717])).

cnf(c_13363,plain,
    ( sK3(k7_lattice3(sK4),sK5) != k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5))
    | sK5 != X0_59
    | r2_hidden(k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5)),X0_59) != iProver_top
    | r2_hidden(sK3(k7_lattice3(sK4),sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13362])).

cnf(c_13365,plain,
    ( sK3(k7_lattice3(sK4),sK5) != k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))
    | sK5 != sK5
    | r2_hidden(k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5)),sK5) != iProver_top
    | r2_hidden(sK3(k7_lattice3(sK4),sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13363])).

cnf(c_8722,plain,
    ( ~ r2_hidden(X0_59,X1_59)
    | r2_hidden(sK2(k7_lattice3(sK4),sK5),sK5)
    | sK2(k7_lattice3(sK4),sK5) != X0_59
    | sK5 != X1_59 ),
    inference(instantiation,[status(thm)],[c_7528])).

cnf(c_13375,plain,
    ( ~ r2_hidden(k9_lattice3(X0_60,sK2(k7_lattice3(sK4),sK5)),X0_59)
    | r2_hidden(sK2(k7_lattice3(sK4),sK5),sK5)
    | sK2(k7_lattice3(sK4),sK5) != k9_lattice3(X0_60,sK2(k7_lattice3(sK4),sK5))
    | sK5 != X0_59 ),
    inference(instantiation,[status(thm)],[c_8722])).

cnf(c_13376,plain,
    ( sK2(k7_lattice3(sK4),sK5) != k9_lattice3(X0_60,sK2(k7_lattice3(sK4),sK5))
    | sK5 != X0_59
    | r2_hidden(k9_lattice3(X0_60,sK2(k7_lattice3(sK4),sK5)),X0_59) != iProver_top
    | r2_hidden(sK2(k7_lattice3(sK4),sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13375])).

cnf(c_13378,plain,
    ( sK2(k7_lattice3(sK4),sK5) != k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5))
    | sK5 != sK5
    | r2_hidden(k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),sK5) != iProver_top
    | r2_hidden(sK2(k7_lattice3(sK4),sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13376])).

cnf(c_18372,plain,
    ( ~ m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_7509])).

cnf(c_18373,plain,
    ( k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5)
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18372])).

cnf(c_46,negated_conjecture,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | v12_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_6,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k12_lattice3(X1,X3,X2),X0)
    | ~ v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_807,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k12_lattice3(X1,X3,X2),X0)
    | ~ v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_65])).

cnf(c_808,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X1,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k12_lattice3(sK4,X1,X2),X0)
    | ~ v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_807])).

cnf(c_812,plain,
    ( v1_xboole_0(X0)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X1,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k12_lattice3(sK4,X1,X2),X0)
    | ~ v1_waybel_7(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_808,c_69,c_68,c_67,c_64])).

cnf(c_813,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X1,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k12_lattice3(sK4,X2,X1),X0)
    | ~ v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_812])).

cnf(c_1158,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X1,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k12_lattice3(sK4,X1,X2),X0)
    | ~ v1_waybel_7(X0,sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_813,c_411])).

cnf(c_1159,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X1,X0),sK5)
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_1158])).

cnf(c_2603,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,sK5)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK5)
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(resolution,[status(thm)],[c_46,c_1159])).

cnf(c_47,negated_conjecture,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | v1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_44,negated_conjecture,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_2606,plain,
    ( ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK5)
    | r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5)
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2603,c_47,c_45,c_44])).

cnf(c_2607,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,sK5)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X1,X0),sK5) ),
    inference(renaming,[status(thm)],[c_2606])).

cnf(c_7491,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0_59,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_59,u1_struct_0(sK4))
    | r2_hidden(X1_59,sK5)
    | r2_hidden(X0_59,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X1_59,X0_59),sK5) ),
    inference(subtyping,[status(esa)],[c_2607])).

cnf(c_7997,plain,
    ( ~ m1_subset_1(X0_59,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_59,u1_struct_0(sK4))
    | r2_hidden(X1_59,sK5)
    | r2_hidden(X0_59,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X1_59,X0_59),sK5)
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(bin_hyper_res,[status(thm)],[c_7491,c_7889])).

cnf(c_12913,plain,
    ( ~ m1_subset_1(X0_59,u1_struct_0(sK4))
    | ~ m1_subset_1(k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5)),u1_struct_0(sK4))
    | r2_hidden(X0_59,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X0_59,k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5))),sK5)
    | r2_hidden(k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5)),sK5)
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_7997])).

cnf(c_37085,plain,
    ( ~ m1_subset_1(k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),u1_struct_0(sK4))
    | ~ r2_hidden(k12_lattice3(sK4,k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5))),sK5)
    | r2_hidden(k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5)),sK5)
    | r2_hidden(k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),sK5)
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_12913])).

cnf(c_37109,plain,
    ( m1_subset_1(k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k12_lattice3(sK4,k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5))),sK5) != iProver_top
    | r2_hidden(k9_lattice3(X0_60,sK3(k7_lattice3(sK4),sK5)),sK5) = iProver_top
    | r2_hidden(k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),sK5) = iProver_top
    | v1_waybel_7(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37085])).

cnf(c_37111,plain,
    ( m1_subset_1(k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5)),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k12_lattice3(sK4,k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))),sK5) != iProver_top
    | r2_hidden(k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),sK5) = iProver_top
    | r2_hidden(k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5)),sK5) = iProver_top
    | v1_waybel_7(sK5,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37109])).

cnf(c_37200,plain,
    ( k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36850,c_70,c_71,c_72,c_75,c_94,c_2948,c_3015,c_3016,c_3017,c_3018,c_3019,c_3788,c_4053,c_7561,c_7563,c_7564,c_7574,c_7583,c_7586,c_7589,c_7608,c_9372,c_9375,c_9494,c_9576,c_9579,c_9661,c_10318,c_10321,c_10330,c_10340,c_13365,c_13378,c_18373,c_37111])).

cnf(c_37212,plain,
    ( m1_subset_1(sK1(sK4,sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_37200,c_8550])).

cnf(c_37215,plain,
    ( m1_subset_1(sK1(sK4,sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37212,c_70,c_71,c_72,c_75,c_94,c_2948,c_3015,c_3016,c_3017,c_3018,c_3019,c_3788,c_4053,c_7561,c_7563,c_7564,c_7574,c_7583,c_7586,c_7589,c_7608,c_9372,c_9375,c_9494,c_9576,c_9579,c_9661,c_10318,c_10321,c_10330,c_10340,c_13365,c_13378,c_37111])).

cnf(c_37235,plain,
    ( k12_lattice3(sK4,k9_lattice3(sK4,X0_59),k9_lattice3(sK4,sK1(sK4,sK5))) = k13_lattice3(k7_lattice3(sK4),X0_59,sK1(sK4,sK5))
    | m1_subset_1(X0_59,u1_struct_0(k7_lattice3(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_37215,c_8563])).

cnf(c_37449,plain,
    ( k12_lattice3(sK4,k9_lattice3(sK4,sK1(sK4,sK5)),k9_lattice3(sK4,sK1(sK4,sK5))) = k13_lattice3(k7_lattice3(sK4),sK1(sK4,sK5),sK1(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_37215,c_37235])).

cnf(c_8565,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(X0_59,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_59,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1_59,sK5) = iProver_top
    | r2_hidden(X0_59,sK5) = iProver_top
    | r2_hidden(k12_lattice3(sK4,X0_59,X1_59),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7491])).

cnf(c_37459,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(k9_lattice3(sK4,sK1(sK4,sK5)),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k13_lattice3(k7_lattice3(sK4),sK1(sK4,sK5),sK1(sK4,sK5)),sK5) != iProver_top
    | r2_hidden(k9_lattice3(sK4,sK1(sK4,sK5)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_37449,c_8565])).

cnf(c_37463,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37459,c_70,c_71,c_72,c_75,c_94,c_2948,c_3015,c_3016,c_3017,c_3018,c_3019,c_3788,c_7563,c_7574,c_7583,c_7586,c_7589,c_9372,c_9375,c_9494,c_9576,c_9579,c_9661,c_10318,c_10321,c_10330,c_10340,c_13365,c_13378,c_37111])).

cnf(c_37468,plain,
    ( v1_waybel_7(sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_37463,c_9090])).

cnf(c_37474,plain,
    ( k8_lattice3(sK4,sK0(sK4,sK5)) = sK0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_10572,c_37468])).

cnf(c_41672,plain,
    ( m1_subset_1(sK0(sK4,sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_37474,c_8550])).

cnf(c_4014,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_3737,c_3793])).

cnf(c_4015,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4014])).

cnf(c_41679,plain,
    ( m1_subset_1(sK0(sK4,sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41672,c_70,c_71,c_72,c_75,c_94,c_2948,c_3015,c_3016,c_3017,c_3018,c_3019,c_3788,c_4015,c_7561,c_7563,c_7564,c_7574,c_7583,c_7586,c_7589,c_7608,c_9372,c_9375,c_9494,c_9576,c_9579,c_9661,c_10318,c_10321,c_10330,c_10340,c_13365,c_13378,c_37111])).

cnf(c_37276,plain,
    ( k9_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5)
    | l1_orders_2(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_37215,c_8548])).

cnf(c_9321,plain,
    ( k9_lattice3(X0_60,k8_lattice3(X0_60,X0_59)) = k8_lattice3(X0_60,X0_59)
    | m1_subset_1(X0_59,u1_struct_0(X0_60)) != iProver_top
    | l1_orders_2(X0_60) != iProver_top ),
    inference(superposition,[status(thm)],[c_8550,c_8548])).

cnf(c_10429,plain,
    ( k9_lattice3(sK4,k8_lattice3(sK4,sK1(sK4,sK5))) = k8_lattice3(sK4,sK1(sK4,sK5))
    | v1_waybel_7(sK5,sK4) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10424,c_9321])).

cnf(c_24674,plain,
    ( v1_waybel_7(sK5,sK4) = iProver_top
    | k9_lattice3(sK4,k8_lattice3(sK4,sK1(sK4,sK5))) = k8_lattice3(sK4,sK1(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10429,c_75])).

cnf(c_24675,plain,
    ( k9_lattice3(sK4,k8_lattice3(sK4,sK1(sK4,sK5))) = k8_lattice3(sK4,sK1(sK4,sK5))
    | v1_waybel_7(sK5,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_24674])).

cnf(c_37203,plain,
    ( k9_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5)
    | v1_waybel_7(sK5,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_37200,c_24675])).

cnf(c_37731,plain,
    ( k9_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37276,c_70,c_71,c_72,c_75,c_94,c_2948,c_3015,c_3016,c_3017,c_3018,c_3019,c_3788,c_7563,c_7574,c_7583,c_7586,c_7589,c_7755,c_9372,c_9375,c_9494,c_9576,c_9579,c_9661,c_10318,c_10321,c_10330,c_10340,c_13365,c_13378,c_37111,c_37203])).

cnf(c_37735,plain,
    ( k12_lattice3(sK4,k9_lattice3(sK4,X0_59),sK1(sK4,sK5)) = k13_lattice3(k7_lattice3(sK4),X0_59,sK1(sK4,sK5))
    | m1_subset_1(X0_59,u1_struct_0(k7_lattice3(sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_37731,c_37235])).

cnf(c_41692,plain,
    ( k12_lattice3(sK4,k9_lattice3(sK4,sK0(sK4,sK5)),sK1(sK4,sK5)) = k13_lattice3(k7_lattice3(sK4),sK0(sK4,sK5),sK1(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_41679,c_37735])).

cnf(c_10442,plain,
    ( k9_lattice3(sK4,k8_lattice3(sK4,sK0(sK4,sK5))) = k8_lattice3(sK4,sK0(sK4,sK5))
    | v1_waybel_7(sK5,sK4) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10437,c_9321])).

cnf(c_27476,plain,
    ( v1_waybel_7(sK5,sK4) = iProver_top
    | k9_lattice3(sK4,k8_lattice3(sK4,sK0(sK4,sK5))) = k8_lattice3(sK4,sK0(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10442,c_75])).

cnf(c_27477,plain,
    ( k9_lattice3(sK4,k8_lattice3(sK4,sK0(sK4,sK5))) = k8_lattice3(sK4,sK0(sK4,sK5))
    | v1_waybel_7(sK5,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_27476])).

cnf(c_37473,plain,
    ( k9_lattice3(sK4,k8_lattice3(sK4,sK0(sK4,sK5))) = k8_lattice3(sK4,sK0(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_27477,c_37468])).

cnf(c_37475,plain,
    ( k9_lattice3(sK4,sK0(sK4,sK5)) = sK0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_37473,c_37474])).

cnf(c_41901,plain,
    ( k13_lattice3(k7_lattice3(sK4),sK0(sK4,sK5),sK1(sK4,sK5)) = k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_41692,c_37475])).

cnf(c_12,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k13_lattice3(X1,X3,X2),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1191,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k13_lattice3(X1,X3,X2),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_411])).

cnf(c_1192,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | ~ v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,sK5)
    | r2_hidden(X2,sK5)
    | ~ r2_hidden(k13_lattice3(X0,X2,X1),sK5)
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_1191])).

cnf(c_1827,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | ~ v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,sK5)
    | r2_hidden(X2,sK5)
    | ~ r2_hidden(k13_lattice3(X0,X1,X2),sK5)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k7_lattice3(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1192,c_778])).

cnf(c_1828,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5)
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),X1,X0),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(unflattening,[status(thm)],[c_1827])).

cnf(c_3011,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5)
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),X1,X0),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2899,c_1828])).

cnf(c_3022,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK4)))
    | r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5)
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),X1,X0),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2946,c_3011])).

cnf(c_3834,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK4)))
    | r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5)
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),X1,X0),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3786,c_3022])).

cnf(c_7479,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0_59,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1_59,u1_struct_0(k7_lattice3(sK4)))
    | r2_hidden(X1_59,sK5)
    | r2_hidden(X0_59,sK5)
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),X1_59,X0_59),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(subtyping,[status(esa)],[c_3834])).

cnf(c_7512,plain,
    ( ~ m1_subset_1(X0_59,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1_59,u1_struct_0(k7_lattice3(sK4)))
    | r2_hidden(X1_59,sK5)
    | r2_hidden(X0_59,sK5)
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),X1_59,X0_59),sK5)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_7479])).

cnf(c_8579,plain,
    ( m1_subset_1(X0_59,u1_struct_0(k7_lattice3(sK4))) != iProver_top
    | m1_subset_1(X1_59,u1_struct_0(k7_lattice3(sK4))) != iProver_top
    | r2_hidden(X1_59,sK5) = iProver_top
    | r2_hidden(X0_59,sK5) = iProver_top
    | r2_hidden(k13_lattice3(k7_lattice3(sK4),X0_59,X1_59),sK5) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7512])).

cnf(c_69366,plain,
    ( m1_subset_1(sK0(sK4,sK5),u1_struct_0(k7_lattice3(sK4))) != iProver_top
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(k7_lattice3(sK4))) != iProver_top
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5) != iProver_top
    | r2_hidden(sK0(sK4,sK5),sK5) = iProver_top
    | r2_hidden(sK1(sK4,sK5),sK5) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_41901,c_8579])).

cnf(c_7513,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4))
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_7479])).

cnf(c_7621,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7513])).

cnf(c_1,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_969,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_65])).

cnf(c_970,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_969])).

cnf(c_974,plain,
    ( v1_xboole_0(X0)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,X0),X0)
    | v1_waybel_7(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_970,c_69,c_68,c_67,c_64])).

cnf(c_975,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_974])).

cnf(c_1063,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_975,c_411])).

cnf(c_1064,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_1063])).

cnf(c_2833,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_1064])).

cnf(c_2834,plain,
    ( ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2833])).

cnf(c_2836,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_0(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2834,c_64,c_50,c_40])).

cnf(c_2837,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_2836])).

cnf(c_3665,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_2837])).

cnf(c_3666,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3665])).

cnf(c_3668,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3666,c_64,c_55,c_39,c_2944])).

cnf(c_3669,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3668])).

cnf(c_4166,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5) ),
    inference(resolution,[status(thm)],[c_3669,c_3793])).

cnf(c_4167,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(sK4,sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4166])).

cnf(c_2,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK0(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_939,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK0(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_65])).

cnf(c_940,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_939])).

cnf(c_944,plain,
    ( v1_xboole_0(X0)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,X0),X0)
    | v1_waybel_7(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_940,c_69,c_68,c_67,c_64])).

cnf(c_945,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_944])).

cnf(c_1082,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_945,c_411])).

cnf(c_1083,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_1082])).

cnf(c_2813,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_1083])).

cnf(c_2814,plain,
    ( ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2813])).

cnf(c_2816,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_0(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2814,c_64,c_50,c_40])).

cnf(c_2817,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_2816])).

cnf(c_3682,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_2817])).

cnf(c_3683,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3682])).

cnf(c_3685,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3683,c_64,c_55,c_39,c_2944])).

cnf(c_3686,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3685])).

cnf(c_4128,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5) ),
    inference(resolution,[status(thm)],[c_3686,c_3793])).

cnf(c_4129,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK0(sK4,sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4128])).

cnf(c_3,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k12_lattice3(X1,sK0(X1,X0),sK1(X1,X0)),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_909,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k12_lattice3(X1,sK0(X1,X0),sK1(X1,X0)),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_65])).

cnf(c_910,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,X0),sK1(sK4,X0)),X0)
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_909])).

cnf(c_914,plain,
    ( v1_xboole_0(X0)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,X0),sK1(sK4,X0)),X0)
    | v1_waybel_7(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_910,c_69,c_68,c_67,c_64])).

cnf(c_915,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,X0),sK1(sK4,X0)),X0)
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_914])).

cnf(c_1101,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,X0),sK1(sK4,X0)),X0)
    | v1_waybel_7(X0,sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_915,c_411])).

cnf(c_1102,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_1101])).

cnf(c_2793,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_1102])).

cnf(c_2794,plain,
    ( ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2793])).

cnf(c_2796,plain,
    ( v1_waybel_7(sK5,sK4)
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_0(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2794,c_64,c_50,c_40])).

cnf(c_2797,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_2796])).

cnf(c_3699,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_2797])).

cnf(c_3700,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3699])).

cnf(c_3702,plain,
    ( v1_waybel_7(sK5,sK4)
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3700,c_64,c_55,c_39,c_2944])).

cnf(c_3703,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3702])).

cnf(c_4090,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5) ),
    inference(resolution,[status(thm)],[c_3703,c_3793])).

cnf(c_4091,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4090])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_69366,c_41672,c_37463,c_37215,c_7621,c_7608,c_7589,c_7586,c_7583,c_7574,c_7564,c_7561,c_4167,c_4129,c_4091,c_4015,c_2948,c_75,c_72,c_71,c_70])).


%------------------------------------------------------------------------------
