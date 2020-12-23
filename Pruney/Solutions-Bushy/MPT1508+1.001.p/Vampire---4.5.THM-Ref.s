%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1508+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 358 expanded)
%              Number of leaves         :   11 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  330 (2185 expanded)
%              Number of equality atoms :   14 ( 207 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f190,f252,f255,f281])).

fof(f281,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f27,f247])).

fof(f247,plain,
    ( sK1 = k16_lattice3(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl3_3
  <=> sK1 = k16_lattice3(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f27,plain,(
    sK1 != k16_lattice3(sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r3_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k16_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).

fof(f255,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f25,f249])).

fof(f249,plain,
    ( spl3_4
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f25,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f252,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f239,f179,f249,f245])).

fof(f179,plain,
    ( spl3_1
  <=> r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f239,plain,
    ( ~ r2_hidden(sK1,sK2)
    | sK1 = k16_lattice3(sK0,sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f157,f181])).

fof(f181,plain,
    ( r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f179])).

fof(f157,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK0,sK1,k16_lattice3(sK0,X0))
      | ~ r2_hidden(sK1,X0)
      | sK1 = k16_lattice3(sK0,X0) ) ),
    inference(global_subsumption,[],[f29,f58,f88,f28,f66,f155])).

fof(f155,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | v2_struct_0(sK0)
      | ~ v4_lattices(sK0)
      | ~ l2_lattices(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
      | ~ r1_lattices(sK0,sK1,k16_lattice3(sK0,X0))
      | sK1 = k16_lattice3(sK0,X0) ) ),
    inference(resolution,[],[f154,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X2,X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

fof(f154,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k16_lattice3(sK0,X0),sK1)
      | ~ r2_hidden(sK1,X0) ) ),
    inference(global_subsumption,[],[f29,f32,f59,f60,f61,f28,f66,f153])).

fof(f153,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | r1_lattices(sK0,k16_lattice3(sK0,X0),sK1) ) ),
    inference(resolution,[],[f131,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f131,plain,(
    ! [X3] :
      ( r3_lattices(sK0,k16_lattice3(sK0,X3),sK1)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(global_subsumption,[],[f29,f30,f31,f32,f124])).

fof(f124,plain,(
    ! [X3] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ l3_lattices(sK0)
      | ~ r2_hidden(sK1,X3)
      | r3_lattices(sK0,k16_lattice3(sK0,X3),sK1) ) ),
    inference(resolution,[],[f28,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,X2)
      | r3_lattices(X0,k16_lattice3(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

fof(f31,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,(
    v9_lattices(sK0) ),
    inference(global_subsumption,[],[f32,f30,f51])).

fof(f51,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(resolution,[],[f29,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f60,plain,(
    v8_lattices(sK0) ),
    inference(global_subsumption,[],[f32,f30,f50])).

fof(f50,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v8_lattices(sK0) ),
    inference(resolution,[],[f29,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    v6_lattices(sK0) ),
    inference(global_subsumption,[],[f32,f30,f49])).

fof(f49,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(resolution,[],[f29,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X8] : m1_subset_1(k16_lattice3(sK0,X8),u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f32,f56])).

fof(f56,plain,(
    ! [X8] :
      ( ~ l3_lattices(sK0)
      | m1_subset_1(k16_lattice3(sK0,X8),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f29,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f28,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f88,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f32,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f58,plain,(
    v4_lattices(sK0) ),
    inference(global_subsumption,[],[f32,f30,f48])).

fof(f48,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v4_lattices(sK0) ),
    inference(resolution,[],[f29,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f190,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f26,f187])).

fof(f187,plain,
    ( ~ r3_lattice3(sK0,sK1,sK2)
    | spl3_1 ),
    inference(resolution,[],[f180,f160])).

fof(f160,plain,(
    ! [X0] :
      ( r1_lattices(sK0,sK1,k16_lattice3(sK0,X0))
      | ~ r3_lattice3(sK0,sK1,X0) ) ),
    inference(global_subsumption,[],[f29,f32,f59,f60,f61,f28,f66,f159])).

fof(f159,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK0,sK1,X0)
      | v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
      | r1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) ) ),
    inference(resolution,[],[f132,f47])).

fof(f132,plain,(
    ! [X4] :
      ( r3_lattices(sK0,sK1,k16_lattice3(sK0,X4))
      | ~ r3_lattice3(sK0,sK1,X4) ) ),
    inference(global_subsumption,[],[f29,f30,f31,f32,f125])).

fof(f125,plain,(
    ! [X4] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ l3_lattices(sK0)
      | ~ r3_lattice3(sK0,sK1,X4)
      | r3_lattices(sK0,sK1,k16_lattice3(sK0,X4)) ) ),
    inference(resolution,[],[f28,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).

fof(f180,plain,
    ( ~ r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f179])).

fof(f26,plain,(
    r3_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
