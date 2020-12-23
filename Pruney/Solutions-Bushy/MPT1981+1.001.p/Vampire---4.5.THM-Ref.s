%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1981+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:01 EST 2020

% Result     : Theorem 5.57s
% Output     : Refutation 5.57s
% Verified   : 
% Statistics : Number of formulae       :  281 (31580 expanded)
%              Number of leaves         :   31 (8927 expanded)
%              Depth                    :   54
%              Number of atoms          : 1457 (428433 expanded)
%              Number of equality atoms :   46 (2029 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13795,plain,(
    $false ),
    inference(subsumption_resolution,[],[f13381,f12521])).

fof(f12521,plain,(
    r2_hidden(k3_yellow_0(sK2),sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)) ),
    inference(subsumption_resolution,[],[f12520,f270])).

fof(f270,plain,(
    ~ v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f257,f92])).

fof(f92,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,
    ( ! [X2] :
        ( ~ v3_waybel_7(X2,sK2)
        | ~ r1_tarski(sK3,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v13_waybel_0(X2,sK2)
        | ~ v2_waybel_0(X2,sK2)
        | v1_xboole_0(X2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v13_waybel_0(sK3,sK2)
    & v2_waybel_0(sK3,sK2)
    & v1_subset_1(sK3,u1_struct_0(sK2))
    & ~ v1_xboole_0(sK3)
    & l1_orders_2(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v11_waybel_1(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f68,f67])).

fof(f67,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_waybel_7(X2,X0)
                | ~ r1_tarski(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v13_waybel_0(X2,X0)
                | ~ v2_waybel_0(X2,X0)
                | v1_xboole_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_waybel_7(X2,sK2)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
              | ~ v13_waybel_0(X2,sK2)
              | ~ v2_waybel_0(X2,sK2)
              | v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v13_waybel_0(X1,sK2)
          & v2_waybel_0(X1,sK2)
          & v1_subset_1(X1,u1_struct_0(sK2))
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK2)
      & v2_lattice3(sK2)
      & v1_lattice3(sK2)
      & v11_waybel_1(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ~ v3_waybel_7(X2,sK2)
            | ~ r1_tarski(X1,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
            | ~ v13_waybel_0(X2,sK2)
            | ~ v2_waybel_0(X2,sK2)
            | v1_xboole_0(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v13_waybel_0(X1,sK2)
        & v2_waybel_0(X1,sK2)
        & v1_subset_1(X1,u1_struct_0(sK2))
        & ~ v1_xboole_0(X1) )
   => ( ! [X2] :
          ( ~ v3_waybel_7(X2,sK2)
          | ~ r1_tarski(sK3,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
          | ~ v13_waybel_0(X2,sK2)
          | ~ v2_waybel_0(X2,sK2)
          | v1_xboole_0(X2) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v13_waybel_0(sK3,sK2)
      & v2_waybel_0(sK3,sK2)
      & v1_subset_1(sK3,u1_struct_0(sK2))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_waybel_7(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_waybel_7(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v11_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) )
           => ? [X2] :
                ( v3_waybel_7(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v11_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v7_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) )
           => ? [X2] :
                ( v3_waybel_7(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v7_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( v3_waybel_7(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_waybel_7)).

fof(f257,plain,
    ( ~ v2_struct_0(sK2)
    | ~ v2_lattice3(sK2) ),
    inference(resolution,[],[f93,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f93,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f12520,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f12519,f87])).

fof(f87,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f12519,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f12518,f88])).

fof(f88,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f12518,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f12517,f89])).

fof(f89,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f12517,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f12516,f553])).

fof(f553,plain,(
    v1_yellow_0(sK2) ),
    inference(subsumption_resolution,[],[f552,f379])).

fof(f379,plain,(
    sP0(sK2) ),
    inference(subsumption_resolution,[],[f378,f93])).

fof(f378,plain,
    ( sP0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f370,f90])).

fof(f90,plain,(
    v11_waybel_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f370,plain,
    ( sP0(sK2)
    | ~ v11_waybel_1(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f270,f111])).

fof(f111,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f36,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_waybel_1(X0)
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_waybel_1(X0)
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
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
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

fof(f552,plain,
    ( v1_yellow_0(sK2)
    | ~ sP0(sK2) ),
    inference(resolution,[],[f256,f109])).

fof(f109,plain,(
    ! [X0] :
      ( v3_yellow_0(X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f256,plain,
    ( ~ v3_yellow_0(sK2)
    | v1_yellow_0(sK2) ),
    inference(resolution,[],[f93,f101])).

fof(f101,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_yellow_0(X0)
       => v1_yellow_0(X0) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_yellow_0(X0)
       => ( v2_yellow_0(X0)
          & v1_yellow_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_yellow_0)).

fof(f12516,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f12515,f93])).

fof(f12515,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ l1_orders_2(sK2)
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f12514,f8378])).

fof(f8378,plain,(
    ~ v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)) ),
    inference(subsumption_resolution,[],[f2380,f6363])).

fof(f6363,plain,(
    r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3) ),
    inference(subsumption_resolution,[],[f6362,f94])).

fof(f94,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f6362,plain,
    ( r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3)
    | v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f6361,f1153])).

fof(f1153,plain,(
    ~ v1_xboole_0(k1_tarski(k3_yellow_0(sK2))) ),
    inference(backward_demodulation,[],[f581,f830])).

fof(f830,plain,(
    k5_waybel_0(sK2,k3_yellow_0(sK2)) = k1_tarski(k3_yellow_0(sK2)) ),
    inference(subsumption_resolution,[],[f829,f737])).

fof(f737,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f639,f98])).

fof(f98,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f69])).

fof(f639,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f626,f149])).

fof(f149,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP8(X1) ) ),
    inference(cnf_transformation,[],[f149_D])).

fof(f149_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP8(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

fof(f626,plain,(
    ~ sP8(sK3) ),
    inference(resolution,[],[f608,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP8(X1) ) ),
    inference(general_splitting,[],[f145,f149_D])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f608,plain,(
    r2_hidden(sK5(sK3),sK3) ),
    inference(resolution,[],[f315,f126])).

fof(f126,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f7,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f315,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,sK3)
      | r2_hidden(X9,sK3) ) ),
    inference(resolution,[],[f94,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f829,plain,
    ( k5_waybel_0(sK2,k3_yellow_0(sK2)) = k1_tarski(k3_yellow_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f827,f255])).

fof(f255,plain,(
    m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2)) ),
    inference(resolution,[],[f93,f100])).

fof(f100,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f827,plain,
    ( k5_waybel_0(sK2,k3_yellow_0(sK2)) = k1_tarski(k3_yellow_0(sK2))
    | ~ m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(superposition,[],[f826,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f826,plain,(
    k5_waybel_0(sK2,k3_yellow_0(sK2)) = k6_domain_1(u1_struct_0(sK2),k3_yellow_0(sK2)) ),
    inference(subsumption_resolution,[],[f825,f270])).

fof(f825,plain,
    ( k5_waybel_0(sK2,k3_yellow_0(sK2)) = k6_domain_1(u1_struct_0(sK2),k3_yellow_0(sK2))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f274,f553])).

fof(f274,plain,
    ( k5_waybel_0(sK2,k3_yellow_0(sK2)) = k6_domain_1(u1_struct_0(sK2),k3_yellow_0(sK2))
    | ~ v1_yellow_0(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f273,f87])).

fof(f273,plain,
    ( k5_waybel_0(sK2,k3_yellow_0(sK2)) = k6_domain_1(u1_struct_0(sK2),k3_yellow_0(sK2))
    | ~ v1_yellow_0(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f272,f88])).

fof(f272,plain,
    ( k5_waybel_0(sK2,k3_yellow_0(sK2)) = k6_domain_1(u1_struct_0(sK2),k3_yellow_0(sK2))
    | ~ v1_yellow_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f259,f89])).

fof(f259,plain,
    ( k5_waybel_0(sK2,k3_yellow_0(sK2)) = k6_domain_1(u1_struct_0(sK2),k3_yellow_0(sK2))
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f93,f112])).

fof(f112,plain,(
    ! [X0] :
      ( k5_waybel_0(X0,k3_yellow_0(X0)) = k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k5_waybel_0(X0,k3_yellow_0(X0)) = k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k5_waybel_0(X0,k3_yellow_0(X0)) = k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k5_waybel_0(X0,k3_yellow_0(X0)) = k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_4)).

fof(f581,plain,(
    ~ v1_xboole_0(k5_waybel_0(sK2,k3_yellow_0(sK2))) ),
    inference(subsumption_resolution,[],[f580,f270])).

fof(f580,plain,
    ( ~ v1_xboole_0(k5_waybel_0(sK2,k3_yellow_0(sK2)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f579,f87])).

fof(f579,plain,
    ( ~ v1_xboole_0(k5_waybel_0(sK2,k3_yellow_0(sK2)))
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f573,f93])).

fof(f573,plain,
    ( ~ v1_xboole_0(k5_waybel_0(sK2,k3_yellow_0(sK2)))
    | ~ l1_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f255,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).

fof(f6361,plain,
    ( v1_xboole_0(k1_tarski(k3_yellow_0(sK2)))
    | r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3)
    | v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f6345,f619])).

fof(f619,plain,(
    ~ m1_subset_1(k3_yellow_0(sK2),sK3) ),
    inference(subsumption_resolution,[],[f618,f94])).

fof(f618,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(k3_yellow_0(sK2),sK3) ),
    inference(resolution,[],[f609,f131])).

fof(f609,plain,(
    ~ r2_hidden(k3_yellow_0(sK2),sK3) ),
    inference(subsumption_resolution,[],[f493,f553])).

fof(f493,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ v1_yellow_0(sK2) ),
    inference(subsumption_resolution,[],[f492,f270])).

fof(f492,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ v1_yellow_0(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f491,f87])).

fof(f491,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ v1_yellow_0(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f490,f88])).

fof(f490,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ v1_yellow_0(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f489,f89])).

fof(f489,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f488,f93])).

fof(f488,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f487,f94])).

fof(f487,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | v1_xboole_0(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f486,f96])).

fof(f96,plain,(
    v2_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f486,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ v2_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f485,f97])).

fof(f97,plain,(
    v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f485,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ v13_waybel_0(sK3,sK2)
    | ~ v2_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f475,f95])).

fof(f95,plain,(
    v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f69])).

fof(f475,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v13_waybel_0(sK3,sK2)
    | ~ v2_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f98,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k3_yellow_0(X0),X1)
      | ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_subset_1(X1,u1_struct_0(X0))
              | r2_hidden(k3_yellow_0(X0),X1) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f6345,plain,
    ( m1_subset_1(k3_yellow_0(sK2),sK3)
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK2)))
    | r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f2802,f1194])).

fof(f1194,plain,(
    ! [X11] :
      ( ~ r1_subset_1(X11,k1_tarski(k3_yellow_0(sK2)))
      | r1_subset_1(k1_tarski(k3_yellow_0(sK2)),X11)
      | v1_xboole_0(X11) ) ),
    inference(resolution,[],[f1153,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

fof(f2802,plain,(
    ! [X4] :
      ( r1_subset_1(sK3,k1_tarski(X4))
      | m1_subset_1(X4,sK3)
      | v1_xboole_0(k1_tarski(X4)) ) ),
    inference(duplicate_literal_removal,[],[f2789])).

fof(f2789,plain,(
    ! [X4] :
      ( m1_subset_1(X4,sK3)
      | r1_subset_1(sK3,k1_tarski(X4))
      | v1_xboole_0(k1_tarski(X4))
      | r1_subset_1(sK3,k1_tarski(X4))
      | v1_xboole_0(k1_tarski(X4)) ) ),
    inference(superposition,[],[f1329,f1338])).

fof(f1338,plain,(
    ! [X7] :
      ( sK6(sK3,k1_tarski(X7)) = X7
      | r1_subset_1(sK3,k1_tarski(X7))
      | v1_xboole_0(k1_tarski(X7)) ) ),
    inference(resolution,[],[f654,f148])).

fof(f148,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f140])).

fof(f140,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f84,f85])).

fof(f85,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
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
    inference(rectify,[],[f83])).

fof(f83,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f654,plain,(
    ! [X2] :
      ( r2_hidden(sK6(sK3,X2),X2)
      | v1_xboole_0(X2)
      | r1_subset_1(sK3,X2) ) ),
    inference(resolution,[],[f320,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f45,f80])).

fof(f80,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f320,plain,(
    ! [X14] :
      ( ~ r1_xboole_0(sK3,X14)
      | r1_subset_1(sK3,X14)
      | v1_xboole_0(X14) ) ),
    inference(resolution,[],[f94,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f1329,plain,(
    ! [X1] :
      ( m1_subset_1(sK6(sK3,X1),sK3)
      | r1_subset_1(sK3,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f653,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f653,plain,(
    ! [X1] :
      ( r2_hidden(sK6(sK3,X1),sK3)
      | v1_xboole_0(X1)
      | r1_subset_1(sK3,X1) ) ),
    inference(resolution,[],[f320,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f2380,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3)
    | ~ v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)) ),
    inference(resolution,[],[f1253,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK4(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( r1_subset_1(X0,sK4(X0,X1,X2))
        & r1_tarski(X1,sK4(X0,X1,X2))
        & v2_waybel_7(sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v13_waybel_0(sK4(X0,X1,X2),X2)
        & v2_waybel_0(sK4(X0,X1,X2),X2)
        & ~ v1_xboole_0(sK4(X0,X1,X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f73,f74])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_subset_1(X0,X3)
          & r1_tarski(X1,X3)
          & v2_waybel_7(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v13_waybel_0(X3,X2)
          & v2_waybel_0(X3,X2)
          & ~ v1_xboole_0(X3) )
     => ( r1_subset_1(X0,sK4(X0,X1,X2))
        & r1_tarski(X1,sK4(X0,X1,X2))
        & v2_waybel_7(sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v13_waybel_0(sK4(X0,X1,X2),X2)
        & v2_waybel_0(sK4(X0,X1,X2),X2)
        & ~ v1_xboole_0(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r1_subset_1(X0,X3)
          & r1_tarski(X1,X3)
          & v2_waybel_7(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v13_waybel_0(X3,X2)
          & v2_waybel_0(X3,X2)
          & ~ v1_xboole_0(X3) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( r1_subset_1(X1,X3)
          & r1_tarski(X2,X3)
          & v2_waybel_7(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X3,X0)
          & v2_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( r1_subset_1(X1,X3)
          & r1_tarski(X2,X3)
          & v2_waybel_7(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X3,X0)
          & v2_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1253,plain,
    ( sP1(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)
    | ~ r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3) ),
    inference(subsumption_resolution,[],[f1252,f1153])).

fof(f1252,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3)
    | sP1(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK2))) ),
    inference(subsumption_resolution,[],[f1251,f1152])).

fof(f1152,plain,(
    v1_waybel_0(k1_tarski(k3_yellow_0(sK2)),sK2) ),
    inference(backward_demodulation,[],[f584,f830])).

fof(f584,plain,(
    v1_waybel_0(k5_waybel_0(sK2,k3_yellow_0(sK2)),sK2) ),
    inference(subsumption_resolution,[],[f583,f270])).

fof(f583,plain,
    ( v1_waybel_0(k5_waybel_0(sK2,k3_yellow_0(sK2)),sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f582,f87])).

fof(f582,plain,
    ( v1_waybel_0(k5_waybel_0(sK2,k3_yellow_0(sK2)),sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f574,f93])).

fof(f574,plain,
    ( v1_waybel_0(k5_waybel_0(sK2,k3_yellow_0(sK2)),sK2)
    | ~ l1_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f255,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1251,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3)
    | sP1(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)
    | ~ v1_waybel_0(k1_tarski(k3_yellow_0(sK2)),sK2)
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK2))) ),
    inference(subsumption_resolution,[],[f1230,f1151])).

fof(f1151,plain,(
    v12_waybel_0(k1_tarski(k3_yellow_0(sK2)),sK2) ),
    inference(backward_demodulation,[],[f587,f830])).

fof(f587,plain,(
    v12_waybel_0(k5_waybel_0(sK2,k3_yellow_0(sK2)),sK2) ),
    inference(subsumption_resolution,[],[f586,f270])).

fof(f586,plain,
    ( v12_waybel_0(k5_waybel_0(sK2,k3_yellow_0(sK2)),sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f585,f88])).

fof(f585,plain,
    ( v12_waybel_0(k5_waybel_0(sK2,k3_yellow_0(sK2)),sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f575,f93])).

fof(f575,plain,
    ( v12_waybel_0(k5_waybel_0(sK2,k3_yellow_0(sK2)),sK2)
    | ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f255,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).

fof(f1230,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3)
    | sP1(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0(sK2)),sK2)
    | ~ v1_waybel_0(k1_tarski(k3_yellow_0(sK2)),sK2)
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK2))) ),
    inference(resolution,[],[f1149,f887])).

fof(f887,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_subset_1(X0,sK3)
      | sP1(X0,sK3,sK2)
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f502,f538])).

fof(f538,plain,(
    v2_waybel_1(sK2) ),
    inference(resolution,[],[f379,f110])).

fof(f110,plain,(
    ! [X0] :
      ( v2_waybel_1(X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f502,plain,(
    ! [X0] :
      ( sP1(X0,sK3,sK2)
      | ~ r1_subset_1(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | ~ v2_waybel_1(sK2) ) ),
    inference(subsumption_resolution,[],[f501,f87])).

fof(f501,plain,(
    ! [X0] :
      ( sP1(X0,sK3,sK2)
      | ~ r1_subset_1(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | ~ v2_waybel_1(sK2)
      | ~ v3_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f500,f88])).

fof(f500,plain,(
    ! [X0] :
      ( sP1(X0,sK3,sK2)
      | ~ r1_subset_1(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | ~ v2_waybel_1(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f499,f89])).

fof(f499,plain,(
    ! [X0] :
      ( sP1(X0,sK3,sK2)
      | ~ r1_subset_1(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | ~ v2_waybel_1(sK2)
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f498,f91])).

fof(f91,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f498,plain,(
    ! [X0] :
      ( sP1(X0,sK3,sK2)
      | ~ r1_subset_1(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | ~ v1_lattice3(sK2)
      | ~ v2_waybel_1(sK2)
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f497,f92])).

fof(f497,plain,(
    ! [X0] :
      ( sP1(X0,sK3,sK2)
      | ~ r1_subset_1(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | ~ v2_lattice3(sK2)
      | ~ v1_lattice3(sK2)
      | ~ v2_waybel_1(sK2)
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f496,f93])).

fof(f496,plain,(
    ! [X0] :
      ( sP1(X0,sK3,sK2)
      | ~ r1_subset_1(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK2)
      | ~ v2_lattice3(sK2)
      | ~ v1_lattice3(sK2)
      | ~ v2_waybel_1(sK2)
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f495,f94])).

fof(f495,plain,(
    ! [X0] :
      ( sP1(X0,sK3,sK2)
      | ~ r1_subset_1(X0,sK3)
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK2)
      | ~ v2_lattice3(sK2)
      | ~ v1_lattice3(sK2)
      | ~ v2_waybel_1(sK2)
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f494,f96])).

fof(f494,plain,(
    ! [X0] :
      ( sP1(X0,sK3,sK2)
      | ~ r1_subset_1(X0,sK3)
      | ~ v2_waybel_0(sK3,sK2)
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK2)
      | ~ v2_lattice3(sK2)
      | ~ v1_lattice3(sK2)
      | ~ v2_waybel_1(sK2)
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f477,f97])).

fof(f477,plain,(
    ! [X0] :
      ( sP1(X0,sK3,sK2)
      | ~ r1_subset_1(X0,sK3)
      | ~ v13_waybel_0(sK3,sK2)
      | ~ v2_waybel_0(sK3,sK2)
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK2)
      | ~ v2_lattice3(sK2)
      | ~ v1_lattice3(sK2)
      | ~ v2_waybel_1(sK2)
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2) ) ),
    inference(resolution,[],[f98,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X2,X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X2,X0)
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f42,f65])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X1,X3)
                  & r1_tarski(X2,X3)
                  & v2_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v13_waybel_0(X3,X0)
                  & v2_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X1,X3)
                  & r1_tarski(X2,X3)
                  & v2_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v13_waybel_0(X3,X0)
                  & v2_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v13_waybel_0(X3,X0)
                        & v2_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_subset_1(X1,X3)
                          & r1_tarski(X2,X3)
                          & v2_waybel_7(X3,X0) ) )
                  & r1_subset_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_7)).

fof(f1149,plain,(
    m1_subset_1(k1_tarski(k3_yellow_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f589,f830])).

fof(f589,plain,(
    m1_subset_1(k5_waybel_0(sK2,k3_yellow_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f588,f270])).

fof(f588,plain,
    ( m1_subset_1(k5_waybel_0(sK2,k3_yellow_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f576,f93])).

fof(f576,plain,
    ( m1_subset_1(k5_waybel_0(sK2,k3_yellow_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f255,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(f12514,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ l1_orders_2(sK2)
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f12513,f9293])).

fof(f9293,plain,(
    v2_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2) ),
    inference(subsumption_resolution,[],[f2381,f6363])).

fof(f2381,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3)
    | v2_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2) ),
    inference(resolution,[],[f1253,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_0(sK4(X0,X1,X2),X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f12513,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ v2_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ l1_orders_2(sK2)
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f12512,f9348])).

fof(f9348,plain,(
    v13_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2) ),
    inference(subsumption_resolution,[],[f2382,f6363])).

fof(f2382,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3)
    | v13_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2) ),
    inference(resolution,[],[f1253,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( v13_waybel_0(sK4(X0,X1,X2),X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f12512,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ v13_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | ~ v2_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ l1_orders_2(sK2)
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f12509,f10232])).

fof(f10232,plain,(
    m1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f2383,f6363])).

fof(f2383,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3)
    | m1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f1253,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f12509,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ m1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v13_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | ~ v2_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ l1_orders_2(sK2)
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f10372,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f10372,plain,(
    ~ v1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f10371,f87])).

fof(f10371,plain,
    ( ~ v1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),u1_struct_0(sK2))
    | ~ v3_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f10370,f88])).

fof(f10370,plain,
    ( ~ v1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),u1_struct_0(sK2))
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f10369,f89])).

fof(f10369,plain,
    ( ~ v1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f10368,f90])).

fof(f10368,plain,
    ( ~ v1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),u1_struct_0(sK2))
    | ~ v11_waybel_1(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f10367,f91])).

fof(f10367,plain,
    ( ~ v1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),u1_struct_0(sK2))
    | ~ v1_lattice3(sK2)
    | ~ v11_waybel_1(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f10366,f92])).

fof(f10366,plain,
    ( ~ v1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v11_waybel_1(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f10365,f93])).

fof(f10365,plain,
    ( ~ v1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v11_waybel_1(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f10364,f8378])).

fof(f10364,plain,
    ( ~ v1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),u1_struct_0(sK2))
    | v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ l1_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v11_waybel_1(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f10363,f9293])).

fof(f10363,plain,
    ( ~ v1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),u1_struct_0(sK2))
    | ~ v2_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ l1_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v11_waybel_1(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f10362,f9348])).

fof(f10362,plain,
    ( ~ v1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),u1_struct_0(sK2))
    | ~ v13_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | ~ v2_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ l1_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v11_waybel_1(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f10361,f10232])).

fof(f10361,plain,
    ( ~ v1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v13_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | ~ v2_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ l1_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v11_waybel_1(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f10358,f9409])).

fof(f9409,plain,(
    v2_waybel_7(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2) ),
    inference(subsumption_resolution,[],[f2384,f6363])).

fof(f2384,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3)
    | v2_waybel_7(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2) ),
    inference(resolution,[],[f1253,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_7(sK4(X0,X1,X2),X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f10358,plain,
    ( ~ v2_waybel_7(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | ~ v1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v13_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | ~ v2_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ l1_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v11_waybel_1(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[],[f10260,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( v3_waybel_7(X1,X0)
      | ~ v2_waybel_7(X1,X0)
      | ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_waybel_7(X1,X0)
                & v1_subset_1(X1,u1_struct_0(X0)) )
              | ~ v3_waybel_7(X1,X0) )
            & ( v3_waybel_7(X1,X0)
              | ~ v2_waybel_7(X1,X0)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_waybel_7(X1,X0)
                & v1_subset_1(X1,u1_struct_0(X0)) )
              | ~ v3_waybel_7(X1,X0) )
            & ( v3_waybel_7(X1,X0)
              | ~ v2_waybel_7(X1,X0)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0)) )
          <=> v3_waybel_7(X1,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0)) )
          <=> v3_waybel_7(X1,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( ( v2_waybel_7(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0)) )
          <=> v3_waybel_7(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_waybel_7)).

fof(f10260,plain,(
    ~ v3_waybel_7(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2) ),
    inference(subsumption_resolution,[],[f10259,f8378])).

fof(f10259,plain,
    ( ~ v3_waybel_7(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)) ),
    inference(subsumption_resolution,[],[f10258,f9293])).

fof(f10258,plain,
    ( ~ v3_waybel_7(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | ~ v2_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)) ),
    inference(subsumption_resolution,[],[f10257,f9348])).

fof(f10257,plain,
    ( ~ v3_waybel_7(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | ~ v13_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | ~ v2_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)) ),
    inference(subsumption_resolution,[],[f10233,f9423])).

fof(f9423,plain,(
    r1_tarski(sK3,sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)) ),
    inference(subsumption_resolution,[],[f2385,f6363])).

fof(f2385,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3)
    | r1_tarski(sK3,sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)) ),
    inference(resolution,[],[f1253,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,sK4(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f10233,plain,
    ( ~ r1_tarski(sK3,sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2))
    | ~ v3_waybel_7(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | ~ v13_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | ~ v2_waybel_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2),sK2)
    | v1_xboole_0(sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)) ),
    inference(resolution,[],[f10232,f99])).

fof(f99,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(sK3,X2)
      | ~ v3_waybel_7(X2,sK2)
      | ~ v13_waybel_0(X2,sK2)
      | ~ v2_waybel_0(X2,sK2)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f13381,plain,(
    ~ r2_hidden(k3_yellow_0(sK2),sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)) ),
    inference(resolution,[],[f12234,f10373])).

fof(f10373,plain,(
    r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)) ),
    inference(subsumption_resolution,[],[f2386,f6363])).

fof(f2386,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK3)
    | r1_subset_1(k1_tarski(k3_yellow_0(sK2)),sK4(k1_tarski(k3_yellow_0(sK2)),sK3,sK2)) ),
    inference(resolution,[],[f1253,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r1_subset_1(X0,sK4(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f12234,plain,(
    ! [X3] :
      ( ~ r1_subset_1(k1_tarski(k3_yellow_0(sK2)),X3)
      | ~ r2_hidden(k3_yellow_0(sK2),X3) ) ),
    inference(subsumption_resolution,[],[f12233,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f12233,plain,(
    ! [X3] :
      ( ~ r2_hidden(k3_yellow_0(sK2),X3)
      | ~ r1_subset_1(k1_tarski(k3_yellow_0(sK2)),X3)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f12224,f1153])).

fof(f12224,plain,(
    ! [X3] :
      ( ~ r2_hidden(k3_yellow_0(sK2),X3)
      | ~ r1_subset_1(k1_tarski(k3_yellow_0(sK2)),X3)
      | v1_xboole_0(X3)
      | v1_xboole_0(k1_tarski(k3_yellow_0(sK2))) ) ),
    inference(resolution,[],[f10715,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f10715,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_tarski(k3_yellow_0(sK2)),X0)
      | ~ r2_hidden(k3_yellow_0(sK2),X0) ) ),
    inference(forward_demodulation,[],[f10714,f2230])).

fof(f2230,plain,(
    k3_yellow_0(sK2) = sK5(k1_tarski(k3_yellow_0(sK2))) ),
    inference(resolution,[],[f2227,f148])).

fof(f2227,plain,(
    r2_hidden(sK5(k1_tarski(k3_yellow_0(sK2))),k1_tarski(k3_yellow_0(sK2))) ),
    inference(resolution,[],[f1192,f126])).

fof(f1192,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_tarski(k3_yellow_0(sK2)))
      | r2_hidden(X9,k1_tarski(k3_yellow_0(sK2))) ) ),
    inference(resolution,[],[f1153,f131])).

fof(f10714,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(k1_tarski(k3_yellow_0(sK2))),X0)
      | ~ r1_xboole_0(k1_tarski(k3_yellow_0(sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f10712,f255])).

fof(f10712,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(k1_tarski(k3_yellow_0(sK2))),X0)
      | ~ r1_xboole_0(k1_tarski(k3_yellow_0(sK2)),X0)
      | ~ m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2)) ) ),
    inference(superposition,[],[f2582,f830])).

fof(f2582,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK5(k5_waybel_0(sK2,X2)),X3)
      | ~ r1_xboole_0(k5_waybel_0(sK2,X2),X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f1471,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f1471,plain,(
    ! [X2] :
      ( r2_hidden(sK5(k5_waybel_0(sK2,X2)),k5_waybel_0(sK2,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f689,f126])).

fof(f689,plain,(
    ! [X17,X16] :
      ( ~ m1_subset_1(X17,k5_waybel_0(sK2,X16))
      | r2_hidden(X17,k5_waybel_0(sK2,X16))
      | ~ m1_subset_1(X16,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f681,f131])).

fof(f681,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(k5_waybel_0(sK2,X9))
      | ~ m1_subset_1(X9,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f306,f270])).

fof(f306,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(k5_waybel_0(sK2,X9))
      | ~ m1_subset_1(X9,u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f268,f87])).

fof(f268,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(k5_waybel_0(sK2,X9))
      | ~ m1_subset_1(X9,u1_struct_0(sK2))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f93,f134])).

%------------------------------------------------------------------------------
