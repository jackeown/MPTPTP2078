%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 242 expanded)
%              Number of leaves         :   17 (  59 expanded)
%              Depth                    :   42
%              Number of atoms          :  986 (1986 expanded)
%              Number of equality atoms :   31 (  51 expanded)
%              Maximal formula depth    :   22 (  10 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f434,plain,(
    $false ),
    inference(subsumption_resolution,[],[f433,f60])).

fof(f60,plain,(
    v5_waybel_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ v4_waybel_7(sK1,sK0)
    & v5_waybel_6(sK1,sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_waybel_7(X1,X0)
            & v5_waybel_6(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v4_waybel_7(X1,sK0)
          & v5_waybel_6(X1,sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ~ v4_waybel_7(X1,sK0)
        & v5_waybel_6(X1,sK0)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v4_waybel_7(sK1,sK0)
      & v5_waybel_6(sK1,sK0)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

% (8001)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (7998)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (8009)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (8006)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (8009)Refutation not found, incomplete strategy% (8009)------------------------------
% (8009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v5_waybel_6(X1,X0)
             => v4_waybel_7(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v4_waybel_7(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_7)).

fof(f433,plain,(
    ~ v5_waybel_6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f432,f57])).

fof(f57,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f432,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_waybel_6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f431,f61])).

fof(f61,plain,(
    ~ v4_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f431,plain,
    ( v4_waybel_7(sK1,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_waybel_6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f430,f58])).

fof(f58,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f430,plain,
    ( ~ l1_orders_2(sK0)
    | v4_waybel_7(sK1,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_waybel_6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f429,f53])).

fof(f53,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f429,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v4_waybel_7(sK1,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_waybel_6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f428,f54])).

fof(f54,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f428,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v4_waybel_7(sK1,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_waybel_6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f427,f55])).

fof(f55,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f427,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v4_waybel_7(sK1,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_waybel_6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f416,f56])).

fof(f56,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f416,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v4_waybel_7(sK1,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_waybel_6(sK1,sK0) ),
    inference(resolution,[],[f415,f59])).

fof(f59,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f415,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v4_waybel_7(X1,X0)
      | ~ v2_lattice3(X0)
      | ~ v5_waybel_6(X1,X0) ) ),
    inference(subsumption_resolution,[],[f414,f62])).

% (7997)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f62,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f414,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f413,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f413,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ r1_orders_2(X0,X1,X1)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f412])).

fof(f412,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f411,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).

fof(f411,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0) ) ),
    inference(subsumption_resolution,[],[f410,f62])).

fof(f410,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f409])).

fof(f409,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f408,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).

fof(f408,plain,(
    ! [X0,X1] :
      ( ~ v12_waybel_0(k5_waybel_0(X1,X0),X1)
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ r2_hidden(X0,k5_waybel_0(X1,X0))
      | v4_waybel_7(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_waybel_6(X0,X1) ) ),
    inference(subsumption_resolution,[],[f407,f62])).

fof(f407,plain,(
    ! [X0,X1] :
      ( v4_waybel_7(X0,X1)
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ r2_hidden(X0,k5_waybel_0(X1,X0))
      | ~ v12_waybel_0(k5_waybel_0(X1,X0),X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_waybel_6(X0,X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f406])).

fof(f406,plain,(
    ! [X0,X1] :
      ( v4_waybel_7(X0,X1)
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ r2_hidden(X0,k5_waybel_0(X1,X0))
      | ~ v12_waybel_0(k5_waybel_0(X1,X0),X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_waybel_6(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f397,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).

fof(f397,plain,(
    ! [X0,X1] :
      ( ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v4_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f396])).

fof(f396,plain,(
    ! [X0,X1] :
      ( ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v4_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(resolution,[],[f395,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v1_waybel_7(k5_waybel_0(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_7)).

fof(f395,plain,(
    ! [X0,X1] :
      ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v4_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f394,f62])).

fof(f394,plain,(
    ! [X0,X1] :
      ( ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v4_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f387])).

% (8014)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f387,plain,(
    ! [X0,X1] :
      ( ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v4_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f315,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X1,k5_waybel_0(X1,X0),X0)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | r2_lattice3(X1,k5_waybel_0(X1,X0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r2_lattice3(X1,k5_waybel_0(X1,X0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f101,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK2(X1,k5_waybel_0(X0,X2),X3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X1,k5_waybel_0(X0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f100,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X1,k5_waybel_0(X0,X2),X3),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X1,k5_waybel_0(X0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f96,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_waybel_0(X1,X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f89,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK2(X1,k5_waybel_0(X0,X2),X3),X2)
      | ~ m1_subset_1(sK2(X1,k5_waybel_0(X0,X2),X3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X1,k5_waybel_0(X0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f68,f65])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f315,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,k5_waybel_0(X0,X1),X2)
      | ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v4_waybel_7(X2,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f314,f62])).

fof(f314,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v4_waybel_7(X2,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r2_lattice3(X0,k5_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f313,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f313,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v1_xboole_0(k5_waybel_0(X0,X1))
      | v4_waybel_7(X2,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r2_lattice3(X0,k5_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v1_xboole_0(k5_waybel_0(X0,X1))
      | v4_waybel_7(X2,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r2_lattice3(X0,k5_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f210,f89])).

fof(f210,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ v1_waybel_7(X8,X7)
      | ~ v12_waybel_0(X8,X7)
      | ~ v1_waybel_0(X8,X7)
      | v1_xboole_0(X8)
      | v4_waybel_7(X9,X7)
      | ~ l1_orders_2(X7)
      | ~ v2_lattice3(X7)
      | ~ v1_lattice3(X7)
      | ~ v5_orders_2(X7)
      | ~ v4_orders_2(X7)
      | ~ v3_orders_2(X7)
      | ~ r2_hidden(X9,X8)
      | ~ r2_lattice3(X7,X8,X9) ) ),
    inference(subsumption_resolution,[],[f203,f90])).

fof(f203,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ v1_waybel_7(X8,X7)
      | ~ v12_waybel_0(X8,X7)
      | ~ v1_waybel_0(X8,X7)
      | v1_xboole_0(X8)
      | v4_waybel_7(X9,X7)
      | ~ l1_orders_2(X7)
      | ~ v2_lattice3(X7)
      | ~ v1_lattice3(X7)
      | ~ v5_orders_2(X7)
      | ~ v4_orders_2(X7)
      | ~ v3_orders_2(X7)
      | ~ r2_hidden(X9,X8)
      | ~ r2_lattice3(X7,X8,X9) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ v1_waybel_7(X8,X7)
      | ~ v12_waybel_0(X8,X7)
      | ~ v1_waybel_0(X8,X7)
      | v1_xboole_0(X8)
      | v4_waybel_7(X9,X7)
      | ~ l1_orders_2(X7)
      | ~ v2_lattice3(X7)
      | ~ v1_lattice3(X7)
      | ~ v5_orders_2(X7)
      | ~ v4_orders_2(X7)
      | ~ v3_orders_2(X7)
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ l1_orders_2(X7)
      | ~ v5_orders_2(X7)
      | ~ r2_hidden(X9,X8)
      | ~ r2_lattice3(X7,X8,X9) ) ),
    inference(superposition,[],[f93,f185])).

fof(f185,plain,(
    ! [X6,X4,X5] :
      ( k1_yellow_0(X4,X5) = X6
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | ~ r2_hidden(X6,X5)
      | ~ r2_lattice3(X4,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_lattice3(X4,X5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | ~ r2_hidden(X6,X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | k1_yellow_0(X4,X5) = X6
      | k1_yellow_0(X4,X5) = X6
      | ~ r2_lattice3(X4,X5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f111,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK3(X0,X1,X2))
      | k1_yellow_0(X0,X2) = X1
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK3(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK3(X0,X1,X2))
        & r2_lattice3(X0,X2,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,sK3(X0,X2,X1))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f110,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X2) = X1
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,sK3(X0,X2,X1))
      | ~ m1_subset_1(sK3(X0,X2,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,sK3(X0,X2,X1))
      | ~ m1_subset_1(sK3(X0,X2,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f73,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,sK3(X0,X1,X2))
      | k1_yellow_0(X0,X2) = X1
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | v4_waybel_7(k1_yellow_0(X0,X2),X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v4_waybel_7(X1,X0)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ( k1_yellow_0(X0,sK4(X0,X1)) = X1
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(sK4(X0,X1),X0)
                & v12_waybel_0(sK4(X0,X1),X0)
                & v1_waybel_0(sK4(X0,X1),X0)
                & ~ v1_xboole_0(sK4(X0,X1)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_yellow_0(X0,X3) = X1
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X3,X0)
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( k1_yellow_0(X0,sK4(X0,X1)) = X1
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_7(sK4(X0,X1),X0)
        & v12_waybel_0(sK4(X0,X1),X0)
        & v1_waybel_0(sK4(X0,X1),X0)
        & ~ v1_xboole_0(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X3] :
                  ( k1_yellow_0(X0,X3) = X1
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X3,X0)
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X2] :
                  ( k1_yellow_0(X0,X2) = X1
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X2,X0)
                  & v12_waybel_0(X2,X0)
                  & v1_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:51:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (8010)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (8016)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (8000)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (8002)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (7999)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.52  % (8008)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (8011)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (8016)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f434,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f433,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    v5_waybel_6(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    (~v4_waybel_7(sK1,sK0) & v5_waybel_6(sK1,sK0) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f40,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (~v4_waybel_7(X1,sK0) & v5_waybel_6(X1,sK0) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ? [X1] : (~v4_waybel_7(X1,sK0) & v5_waybel_6(X1,sK0) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v4_waybel_7(sK1,sK0) & v5_waybel_6(sK1,sK0) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  % (8001)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.53  % (7998)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (8009)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % (8006)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.54  % (8009)Refutation not found, incomplete strategy% (8009)------------------------------
% 0.22/0.54  % (8009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  fof(f13,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 0.22/0.54    inference(negated_conjecture,[],[f12])).
% 0.22/0.54  fof(f12,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_7)).
% 0.22/0.54  fof(f433,plain,(
% 0.22/0.54    ~v5_waybel_6(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f432,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    v2_lattice3(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f432,plain,(
% 0.22/0.54    ~v2_lattice3(sK0) | ~v5_waybel_6(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f431,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ~v4_waybel_7(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f431,plain,(
% 0.22/0.54    v4_waybel_7(sK1,sK0) | ~v2_lattice3(sK0) | ~v5_waybel_6(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f430,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    l1_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f430,plain,(
% 0.22/0.54    ~l1_orders_2(sK0) | v4_waybel_7(sK1,sK0) | ~v2_lattice3(sK0) | ~v5_waybel_6(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f429,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    v3_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f429,plain,(
% 0.22/0.54    ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | v4_waybel_7(sK1,sK0) | ~v2_lattice3(sK0) | ~v5_waybel_6(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f428,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    v4_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f428,plain,(
% 0.22/0.54    ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | v4_waybel_7(sK1,sK0) | ~v2_lattice3(sK0) | ~v5_waybel_6(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f427,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    v5_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f427,plain,(
% 0.22/0.54    ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | v4_waybel_7(sK1,sK0) | ~v2_lattice3(sK0) | ~v5_waybel_6(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f416,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    v1_lattice3(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f416,plain,(
% 0.22/0.54    ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | v4_waybel_7(sK1,sK0) | ~v2_lattice3(sK0) | ~v5_waybel_6(sK1,sK0)),
% 0.22/0.54    inference(resolution,[],[f415,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f415,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v4_waybel_7(X1,X0) | ~v2_lattice3(X0) | ~v5_waybel_6(X1,X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f414,f62])).
% 0.22/0.54  % (7997)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.22/0.54  fof(f414,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f413,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 0.22/0.54  fof(f413,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | ~r1_orders_2(X0,X1,X1) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f412])).
% 0.22/0.54  fof(f412,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | ~r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(resolution,[],[f411,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_hidden(X2,k5_waybel_0(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).
% 0.22/0.54  fof(f411,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k5_waybel_0(X0,X1)) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f410,f62])).
% 0.22/0.54  fof(f410,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k5_waybel_0(X0,X1)) | v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f409])).
% 0.22/0.54  fof(f409,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k5_waybel_0(X0,X1)) | v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(resolution,[],[f408,f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => v12_waybel_0(k5_waybel_0(X0,X1),X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).
% 0.22/0.54  fof(f408,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v12_waybel_0(k5_waybel_0(X1,X0),X1) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~r2_hidden(X0,k5_waybel_0(X1,X0)) | v4_waybel_7(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v5_waybel_6(X0,X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f407,f62])).
% 0.22/0.54  fof(f407,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v4_waybel_7(X0,X1) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~r2_hidden(X0,k5_waybel_0(X1,X0)) | ~v12_waybel_0(k5_waybel_0(X1,X0),X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v5_waybel_6(X0,X1) | v2_struct_0(X1)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f406])).
% 0.22/0.54  fof(f406,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v4_waybel_7(X0,X1) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~r2_hidden(X0,k5_waybel_0(X1,X0)) | ~v12_waybel_0(k5_waybel_0(X1,X0),X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v5_waybel_6(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.54    inference(resolution,[],[f397,f88])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).
% 0.22/0.54  fof(f397,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v4_waybel_7(X1,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k5_waybel_0(X0,X1)) | ~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f396])).
% 0.22/0.54  fof(f396,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v4_waybel_7(X1,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k5_waybel_0(X0,X1)) | ~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.54    inference(resolution,[],[f395,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v1_waybel_7(k5_waybel_0(X0,X1),X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_7)).
% 0.22/0.54  fof(f395,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v4_waybel_7(X1,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k5_waybel_0(X0,X1)) | ~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f394,f62])).
% 0.22/0.54  fof(f394,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v4_waybel_7(X1,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k5_waybel_0(X0,X1)) | ~v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f387])).
% 0.22/0.54  % (8014)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.54  fof(f387,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v4_waybel_7(X1,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k5_waybel_0(X0,X1)) | ~v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.22/0.54    inference(resolution,[],[f315,f136])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_lattice3(X1,k5_waybel_0(X1,X0),X0) | ~l1_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f135])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | v2_struct_0(X1) | r2_lattice3(X1,k5_waybel_0(X1,X0),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | r2_lattice3(X1,k5_waybel_0(X1,X0),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1)) )),
% 0.22/0.54    inference(resolution,[],[f101,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK2(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(rectify,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,sK2(X1,k5_waybel_0(X0,X2),X3),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | r2_lattice3(X1,k5_waybel_0(X0,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_orders_2(X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f100,f97])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK2(X1,k5_waybel_0(X0,X2),X3),u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X1,k5_waybel_0(X0,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_orders_2(X1)) )),
% 0.22/0.54    inference(resolution,[],[f96,f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_waybel_0(X1,X0)) | ~l1_orders_2(X1) | v2_struct_0(X1) | m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.22/0.54    inference(resolution,[],[f89,f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,sK2(X1,k5_waybel_0(X0,X2),X3),X2) | ~m1_subset_1(sK2(X1,k5_waybel_0(X0,X2),X3),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | r2_lattice3(X1,k5_waybel_0(X0,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_orders_2(X1)) )),
% 0.22/0.54    inference(resolution,[],[f68,f65])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_waybel_0(X0,X1)) | r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f46])).
% 0.22/0.54  fof(f315,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_lattice3(X0,k5_waybel_0(X0,X1),X2) | ~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v4_waybel_7(X2,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X2,k5_waybel_0(X0,X1)) | ~v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f314,f62])).
% 0.22/0.54  fof(f314,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v4_waybel_7(X2,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r2_lattice3(X0,k5_waybel_0(X0,X1),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f313,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_xboole_0(k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f313,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v1_xboole_0(k5_waybel_0(X0,X1)) | v4_waybel_7(X2,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r2_lattice3(X0,k5_waybel_0(X0,X1),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f310])).
% 0.22/0.54  fof(f310,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v1_xboole_0(k5_waybel_0(X0,X1)) | v4_waybel_7(X2,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r2_lattice3(X0,k5_waybel_0(X0,X1),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(resolution,[],[f210,f89])).
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    ( ! [X8,X7,X9] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7))) | ~v1_waybel_7(X8,X7) | ~v12_waybel_0(X8,X7) | ~v1_waybel_0(X8,X7) | v1_xboole_0(X8) | v4_waybel_7(X9,X7) | ~l1_orders_2(X7) | ~v2_lattice3(X7) | ~v1_lattice3(X7) | ~v5_orders_2(X7) | ~v4_orders_2(X7) | ~v3_orders_2(X7) | ~r2_hidden(X9,X8) | ~r2_lattice3(X7,X8,X9)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f203,f90])).
% 0.22/0.54  fof(f203,plain,(
% 0.22/0.54    ( ! [X8,X7,X9] : (~m1_subset_1(X9,u1_struct_0(X7)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7))) | ~v1_waybel_7(X8,X7) | ~v12_waybel_0(X8,X7) | ~v1_waybel_0(X8,X7) | v1_xboole_0(X8) | v4_waybel_7(X9,X7) | ~l1_orders_2(X7) | ~v2_lattice3(X7) | ~v1_lattice3(X7) | ~v5_orders_2(X7) | ~v4_orders_2(X7) | ~v3_orders_2(X7) | ~r2_hidden(X9,X8) | ~r2_lattice3(X7,X8,X9)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f194])).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    ( ! [X8,X7,X9] : (~m1_subset_1(X9,u1_struct_0(X7)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7))) | ~v1_waybel_7(X8,X7) | ~v12_waybel_0(X8,X7) | ~v1_waybel_0(X8,X7) | v1_xboole_0(X8) | v4_waybel_7(X9,X7) | ~l1_orders_2(X7) | ~v2_lattice3(X7) | ~v1_lattice3(X7) | ~v5_orders_2(X7) | ~v4_orders_2(X7) | ~v3_orders_2(X7) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~l1_orders_2(X7) | ~v5_orders_2(X7) | ~r2_hidden(X9,X8) | ~r2_lattice3(X7,X8,X9)) )),
% 0.22/0.54    inference(superposition,[],[f93,f185])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    ( ! [X6,X4,X5] : (k1_yellow_0(X4,X5) = X6 | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v5_orders_2(X4) | ~r2_hidden(X6,X5) | ~r2_lattice3(X4,X5,X6)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f182])).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    ( ! [X6,X4,X5] : (~r2_lattice3(X4,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v5_orders_2(X4) | ~r2_hidden(X6,X5) | ~m1_subset_1(X6,u1_struct_0(X4)) | k1_yellow_0(X4,X5) = X6 | k1_yellow_0(X4,X5) = X6 | ~r2_lattice3(X4,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v5_orders_2(X4)) )),
% 0.22/0.54    inference(resolution,[],[f111,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,sK3(X0,X1,X2)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK3(X0,X1,X2)) & r2_lattice3(X0,X2,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK3(X0,X1,X2)) & r2_lattice3(X0,X2,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.22/0.54    inference(rectify,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,sK3(X0,X2,X1)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_yellow_0(X0,X1) = X2) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f110,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f48])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k1_yellow_0(X0,X1) = X2 | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X3,sK3(X0,X2,X1)) | ~m1_subset_1(sK3(X0,X2,X1),u1_struct_0(X0))) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f109])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k1_yellow_0(X0,X1) = X2 | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X3,sK3(X0,X2,X1)) | ~m1_subset_1(sK3(X0,X2,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(resolution,[],[f73,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_lattice3(X0,X2,sK3(X0,X1,X2)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f48])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X2,X0] : (~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | v4_waybel_7(k1_yellow_0(X0,X2),X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v4_waybel_7(X1,X0) | k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & ((k1_yellow_0(X0,sK4(X0,X1)) = X1 & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK4(X0,X1),X0) & v12_waybel_0(sK4(X0,X1),X0) & v1_waybel_0(sK4(X0,X1),X0) & ~v1_xboole_0(sK4(X0,X1))) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) => (k1_yellow_0(X0,sK4(X0,X1)) = X1 & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK4(X0,X1),X0) & v12_waybel_0(sK4(X0,X1),X0) & v1_waybel_0(sK4(X0,X1),X0) & ~v1_xboole_0(sK4(X0,X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.54    inference(rectify,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (8016)------------------------------
% 0.22/0.54  % (8016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8016)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (8016)Memory used [KB]: 1918
% 0.22/0.54  % (8016)Time elapsed: 0.088 s
% 0.22/0.54  % (8016)------------------------------
% 0.22/0.54  % (8016)------------------------------
% 1.32/0.54  % (7996)Success in time 0.171 s
%------------------------------------------------------------------------------
