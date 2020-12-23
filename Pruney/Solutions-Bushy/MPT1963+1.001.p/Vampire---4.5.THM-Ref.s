%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1963+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 933 expanded)
%              Number of leaves         :   12 ( 243 expanded)
%              Depth                    :   28
%              Number of atoms          :  603 (6683 expanded)
%              Number of equality atoms :    5 (  25 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f471,plain,(
    $false ),
    inference(subsumption_resolution,[],[f470,f379])).

fof(f379,plain,(
    r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(resolution,[],[f347,f159])).

fof(f159,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f158,f44])).

fof(f44,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(f158,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f157,f36])).

fof(f36,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(f157,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f156,f42])).

fof(f42,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v11_waybel_1(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_waybel_7)).

fof(f156,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f83,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v10_waybel_1(X0)
        & v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v10_waybel_1(X0)
        & v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v10_waybel_1(X0)
          & v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc8_waybel_1)).

fof(f83,plain,
    ( ~ v1_lattice3(k3_yellow_1(sK0))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f82,f40])).

fof(f40,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f82,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f81,f44])).

fof(f81,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f67,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ( ~ r2_hidden(k2_xboole_0(sK2,sK3),sK1)
        & r2_hidden(sK3,sK1)
        & r2_hidden(sK2,sK1) )
      | ~ v1_waybel_0(sK1,k3_yellow_1(sK0)) )
    & ( ! [X4,X5] :
          ( r2_hidden(k2_xboole_0(X4,X5),sK1)
          | ~ r2_hidden(X5,sK1)
          | ~ r2_hidden(X4,sK1) )
      | v1_waybel_0(sK1,k3_yellow_1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    & v12_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( ~ r2_hidden(k2_xboole_0(X2,X3),X1)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1) )
          | ~ v1_waybel_0(X1,k3_yellow_1(X0)) )
        & ( ! [X4,X5] :
              ( r2_hidden(k2_xboole_0(X4,X5),X1)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          | v1_waybel_0(X1,k3_yellow_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v12_waybel_0(X1,k3_yellow_1(X0)) )
   => ( ( ? [X3,X2] :
            ( ~ r2_hidden(k2_xboole_0(X2,X3),sK1)
            & r2_hidden(X3,sK1)
            & r2_hidden(X2,sK1) )
        | ~ v1_waybel_0(sK1,k3_yellow_1(sK0)) )
      & ( ! [X5,X4] :
            ( r2_hidden(k2_xboole_0(X4,X5),sK1)
            | ~ r2_hidden(X5,sK1)
            | ~ r2_hidden(X4,sK1) )
        | v1_waybel_0(sK1,k3_yellow_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      & v12_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3,X2] :
        ( ~ r2_hidden(k2_xboole_0(X2,X3),sK1)
        & r2_hidden(X3,sK1)
        & r2_hidden(X2,sK1) )
   => ( ~ r2_hidden(k2_xboole_0(sK2,sK3),sK1)
      & r2_hidden(sK3,sK1)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( ~ r2_hidden(k2_xboole_0(X2,X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | ~ v1_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X4,X5] :
            ( r2_hidden(k2_xboole_0(X4,X5),X1)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | v1_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v12_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( ~ r2_hidden(k2_xboole_0(X2,X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | ~ v1_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X2,X3] :
            ( r2_hidden(k2_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | v1_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v12_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( ~ r2_hidden(k2_xboole_0(X2,X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | ~ v1_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X2,X3] :
            ( r2_hidden(k2_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | v1_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v12_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( v1_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2,X3] :
            ( r2_hidden(k2_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v12_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( v1_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2,X3] :
            ( r2_hidden(k2_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v12_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v12_waybel_0(X1,k3_yellow_1(X0)) )
       => ( v1_waybel_0(X1,k3_yellow_1(X0))
        <=> ! [X2,X3] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => r2_hidden(k2_xboole_0(X2,X3),X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v12_waybel_0(X1,k3_yellow_1(X0)) )
     => ( v1_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X2,X1) )
           => r2_hidden(k2_xboole_0(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_waybel_7)).

fof(f67,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f30,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | r2_hidden(sK5(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              | ( ~ r2_hidden(k13_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
                & r2_hidden(sK5(X0,X1),X1)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f28,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(k13_lattice3(X0,sK4(X0,X1),X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

% (22613)Refutation not found, incomplete strategy% (22613)------------------------------
% (22613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22613)Termination reason: Refutation not found, incomplete strategy

% (22613)Memory used [KB]: 10618
% (22613)Time elapsed: 0.092 s
% (22613)------------------------------
% (22613)------------------------------
fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k13_lattice3(X0,sK4(X0,X1),X3),X1)
          & r2_hidden(X3,X1)
          & r2_hidden(sK4(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k13_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      | ~ r2_hidden(X3,X1)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

% (22599)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_waybel_0)).

fof(f30,plain,(
    v12_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f347,plain,(
    ~ v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f346,f33])).

fof(f33,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f346,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f341,f34])).

fof(f34,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f341,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK3,sK1)
    | ~ v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(resolution,[],[f297,f35])).

fof(f35,plain,
    ( ~ r2_hidden(k2_xboole_0(sK2,sK3),sK1)
    | ~ v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f297,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_xboole_0(X0,X1),sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f296,f93])).

fof(f93,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) ) ),
    inference(resolution,[],[f31,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f296,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_xboole_0(X0,X1),sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f295,f93])).

fof(f295,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_xboole_0(X0,X1),sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f290,f32])).

fof(f32,plain,(
    ! [X4,X5] :
      ( v1_waybel_0(sK1,k3_yellow_1(sK0))
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X4,sK1)
      | r2_hidden(k2_xboole_0(X4,X5),sK1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f290,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_xboole_0(X0,X1),sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ v1_waybel_0(sK1,k3_yellow_1(sK0))
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0))) ) ),
    inference(superposition,[],[f216,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_1)).

fof(f216,plain,(
    ! [X0,X1] :
      ( r2_hidden(k13_lattice3(k3_yellow_1(sK0),X1,X0),sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ v1_waybel_0(sK1,k3_yellow_1(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f215,f93])).

fof(f215,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ v1_waybel_0(sK1,k3_yellow_1(sK0))
      | r2_hidden(k13_lattice3(k3_yellow_1(sK0),X1,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f214,f93])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ v1_waybel_0(sK1,k3_yellow_1(sK0))
      | r2_hidden(k13_lattice3(k3_yellow_1(sK0),X1,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f213,f44])).

fof(f213,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ v1_waybel_0(sK1,k3_yellow_1(sK0))
      | r2_hidden(k13_lattice3(k3_yellow_1(sK0),X1,X0),sK1)
      | ~ l1_orders_2(k3_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f212,f36])).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ v1_waybel_0(sK1,k3_yellow_1(sK0))
      | r2_hidden(k13_lattice3(k3_yellow_1(sK0),X1,X0),sK1)
      | v2_struct_0(k3_yellow_1(sK0))
      | ~ l1_orders_2(k3_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f211,f42])).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ v1_waybel_0(sK1,k3_yellow_1(sK0))
      | r2_hidden(k13_lattice3(k3_yellow_1(sK0),X1,X0),sK1)
      | ~ v11_waybel_1(k3_yellow_1(sK0))
      | v2_struct_0(k3_yellow_1(sK0))
      | ~ l1_orders_2(k3_yellow_1(sK0)) ) ),
    inference(resolution,[],[f71,f49])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(k3_yellow_1(sK0))
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ v1_waybel_0(sK1,k3_yellow_1(sK0))
      | r2_hidden(k13_lattice3(k3_yellow_1(sK0),X0,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f70,f40])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(k13_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ v1_waybel_0(sK1,k3_yellow_1(sK0))
      | ~ v1_lattice3(k3_yellow_1(sK0))
      | ~ v5_orders_2(k3_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f69,f44])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(k13_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ v1_waybel_0(sK1,k3_yellow_1(sK0))
      | ~ l1_orders_2(k3_yellow_1(sK0))
      | ~ v1_lattice3(k3_yellow_1(sK0))
      | ~ v5_orders_2(k3_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f63,f31])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(k13_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK0)))
      | ~ v1_waybel_0(sK1,k3_yellow_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      | ~ l1_orders_2(k3_yellow_1(sK0))
      | ~ v1_lattice3(k3_yellow_1(sK0))
      | ~ v5_orders_2(k3_yellow_1(sK0)) ) ),
    inference(resolution,[],[f30,f54])).

fof(f54,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f470,plain,(
    ~ r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f469,f380])).

fof(f380,plain,(
    r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(resolution,[],[f347,f155])).

fof(f155,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f154,f44])).

fof(f154,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f153,f36])).

fof(f153,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f152,f42])).

fof(f152,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f80,f49])).

fof(f80,plain,
    ( ~ v1_lattice3(k3_yellow_1(sK0))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f79,f40])).

fof(f79,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f78,f44])).

fof(f78,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f66,f31])).

fof(f66,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f30,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f469,plain,
    ( ~ r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f467,f347])).

fof(f467,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    inference(resolution,[],[f283,f297])).

fof(f283,plain,
    ( ~ r2_hidden(k2_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f282,f163])).

fof(f163,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f162,f44])).

fof(f162,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f161,f36])).

fof(f161,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f160,f42])).

fof(f160,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f74,f49])).

fof(f74,plain,
    ( ~ v1_lattice3(k3_yellow_1(sK0))
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f73,f40])).

fof(f73,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f72,f44])).

fof(f72,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f64,f31])).

fof(f64,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f30,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f282,plain,
    ( ~ r2_hidden(k2_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f281,f193])).

fof(f193,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f192,f44])).

fof(f192,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f191,f36])).

fof(f191,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f190,f42])).

fof(f190,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f77,f49])).

fof(f77,plain,
    ( ~ v1_lattice3(k3_yellow_1(sK0))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f76,f40])).

fof(f76,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f75,f44])).

fof(f75,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f65,f31])).

fof(f65,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f30,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f281,plain,
    ( ~ r2_hidden(k2_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(superposition,[],[f197,f60])).

fof(f197,plain,
    ( ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f196,f44])).

fof(f196,plain,
    ( ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f195,f36])).

fof(f195,plain,
    ( ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f194,f42])).

fof(f194,plain,
    ( ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v11_waybel_1(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f86,f49])).

fof(f86,plain,
    ( ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f85,f40])).

fof(f85,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f84,f44])).

fof(f84,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f68,f31])).

fof(f68,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f30,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | ~ r2_hidden(k13_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------
