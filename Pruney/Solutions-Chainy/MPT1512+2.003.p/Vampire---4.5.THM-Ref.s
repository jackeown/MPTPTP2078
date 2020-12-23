%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   96 (1639 expanded)
%              Number of leaves         :   14 ( 330 expanded)
%              Depth                    :   14
%              Number of atoms          :  435 (8963 expanded)
%              Number of equality atoms :   14 (  68 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f181,f239])).

fof(f239,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f41,f39,f40,f42,f199,f195,f210,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,X2)
      | r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

fof(f210,plain,
    ( ~ r3_lattices(sK0,sK6(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f101,f104,f39,f103,f42,f97,f195,f197,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f197,plain,
    ( ~ r1_lattices(sK0,sK6(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f39,f42,f97,f193,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattices(X0,sK6(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(f193,plain,
    ( ~ r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f41,f39,f40,f42,f97,f191,f78])).

fof(f78,plain,(
    ! [X2,X3,X1] :
      ( ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r4_lattice3(X1,X3,X2)
      | r2_hidden(X3,a_2_2_lattice3(X1,X2)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | ~ r4_lattice3(X1,X3,X2)
      | r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(f191,plain,
    ( ~ r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1))
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f42,f39,f142,f97,f97,f184,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | r1_lattices(X0,X1,X3)
      | ~ r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(f184,plain,
    ( ~ r1_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f104,f101,f39,f103,f42,f97,f97,f131,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f131,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl8_5
  <=> r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f142,plain,(
    ! [X0] : r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0)) ),
    inference(superposition,[],[f137,f98])).

fof(f98,plain,(
    ! [X0] : k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f39,f42,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

fof(f137,plain,(
    ! [X0] : r3_lattice3(sK0,k16_lattice3(sK0,X0),X0) ),
    inference(unit_resulting_resolution,[],[f40,f41,f42,f39,f96,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | r3_lattice3(X0,k16_lattice3(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(f96,plain,(
    ! [X0] : m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f39,f42,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f39,f42,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f103,plain,(
    v8_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f40,f39,f42,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f104,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f40,f39,f42,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f101,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f40,f39,f42,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f195,plain,
    ( m1_subset_1(sK6(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f42,f39,f97,f193,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f199,plain,
    ( r2_hidden(sK6(sK0,k15_lattice3(sK0,sK2),sK1),sK2)
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f38,f196,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f196,plain,
    ( r2_hidden(sK6(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f39,f42,f97,f193,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X2),X2)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
              & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).

fof(f42,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f181,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f42,f39,f137,f96,f159,f146,f148,f58])).

fof(f148,plain,
    ( ~ r1_lattices(sK0,k16_lattice3(sK0,sK2),sK5(sK0,k16_lattice3(sK0,sK2),sK1))
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f39,f42,f96,f140,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,sK5(X0,X1,X2))
      | r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f140,plain,
    ( ~ r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1)
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f41,f42,f39,f40,f96,f96,f127,f77])).

fof(f77,plain,(
    ! [X2,X0,X3] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X3,X2)
      | r3_lattices(X0,X3,k16_lattice3(X0,X2)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X3,X2)
      | r3_lattices(X0,X3,X1)
      | k16_lattice3(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f127,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_4
  <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f146,plain,
    ( m1_subset_1(sK5(sK0,k16_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f42,f39,f96,f140,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f159,plain,
    ( r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),sK2)
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f38,f147,f55])).

fof(f147,plain,
    ( r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),sK1)
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f39,f42,f96,f140,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X2),X2)
      | r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f132,plain,
    ( ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f37,f129,f125])).

fof(f37,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:10:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (30936)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.50  % (30957)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (30940)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (30939)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (30947)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (30948)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (30949)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (30964)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (30959)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (30951)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (30955)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (30960)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (30941)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (30938)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (30946)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (30961)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (30943)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (30956)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (30937)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (30942)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (30940)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 1.41/0.54  % (30953)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.54  % (30963)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.54  % (30952)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.54  % (30954)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.55  % (30953)Refutation not found, incomplete strategy% (30953)------------------------------
% 1.41/0.55  % (30953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (30945)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.55  % (30944)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.56  % (30953)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (30953)Memory used [KB]: 10618
% 1.41/0.56  % (30953)Time elapsed: 0.143 s
% 1.41/0.56  % (30953)------------------------------
% 1.41/0.56  % (30953)------------------------------
% 1.41/0.56  % (30965)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.53/0.56  % SZS output start Proof for theBenchmark
% 1.53/0.56  fof(f240,plain,(
% 1.53/0.56    $false),
% 1.53/0.56    inference(avatar_sat_refutation,[],[f132,f181,f239])).
% 1.53/0.56  fof(f239,plain,(
% 1.53/0.56    spl8_5),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f237])).
% 1.53/0.56  fof(f237,plain,(
% 1.53/0.56    $false | spl8_5),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f41,f39,f40,f42,f199,f195,f210,f44])).
% 1.53/0.56  fof(f44,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_hidden(X1,X2) | r3_lattices(X0,X1,k15_lattice3(X0,X2))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f19])).
% 1.53/0.56  fof(f19,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.53/0.56    inference(flattening,[],[f18])).
% 1.53/0.56  fof(f18,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f11])).
% 1.53/0.56  fof(f11,axiom,(
% 1.53/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).
% 1.53/0.56  fof(f210,plain,(
% 1.53/0.56    ~r3_lattices(sK0,sK6(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2)) | spl8_5),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f101,f104,f39,f103,f42,f97,f195,f197,f47])).
% 1.53/0.56  fof(f47,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f21])).
% 1.53/0.56  fof(f21,plain,(
% 1.53/0.56    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.53/0.56    inference(flattening,[],[f20])).
% 1.53/0.56  fof(f20,plain,(
% 1.53/0.56    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f3])).
% 1.53/0.56  fof(f3,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.53/0.56  fof(f197,plain,(
% 1.53/0.56    ~r1_lattices(sK0,sK6(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2)) | spl8_5),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f39,f42,f97,f193,f65])).
% 1.53/0.56  fof(f65,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_lattices(X0,sK6(X0,X1,X2),X1) | r4_lattice3(X0,X1,X2)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f32])).
% 1.53/0.56  fof(f32,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.53/0.56    inference(flattening,[],[f31])).
% 1.53/0.56  fof(f31,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f5])).
% 1.53/0.56  fof(f5,axiom,(
% 1.53/0.56    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 1.53/0.56  fof(f193,plain,(
% 1.53/0.56    ~r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1) | spl8_5),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f41,f39,f40,f42,f97,f191,f78])).
% 1.53/0.56  fof(f78,plain,(
% 1.53/0.56    ( ! [X2,X3,X1] : (~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~r4_lattice3(X1,X3,X2) | r2_hidden(X3,a_2_2_lattice3(X1,X2))) )),
% 1.53/0.56    inference(equality_resolution,[],[f75])).
% 1.53/0.56  fof(f75,plain,(
% 1.53/0.56    ( ! [X2,X0,X3,X1] : (v2_struct_0(X1) | ~v10_lattices(X1) | ~v4_lattice3(X1) | ~l3_lattices(X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | X0 != X3 | ~r4_lattice3(X1,X3,X2) | r2_hidden(X0,a_2_2_lattice3(X1,X2))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f36])).
% 1.53/0.56  fof(f36,plain,(
% 1.53/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.53/0.56    inference(flattening,[],[f35])).
% 1.53/0.56  fof(f35,plain,(
% 1.53/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 1.53/0.56    inference(ennf_transformation,[],[f8])).
% 1.53/0.56  fof(f8,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 1.53/0.56  fof(f191,plain,(
% 1.53/0.56    ~r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1)) | spl8_5),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f42,f39,f142,f97,f97,f184,f58])).
% 1.53/0.56  fof(f58,plain,(
% 1.53/0.56    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X2) | r1_lattices(X0,X1,X3) | ~r3_lattice3(X0,X1,X2)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f30])).
% 1.53/0.56  fof(f30,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.53/0.56    inference(flattening,[],[f29])).
% 1.53/0.56  fof(f29,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f4])).
% 1.53/0.56  fof(f4,axiom,(
% 1.53/0.56    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 1.53/0.56  fof(f184,plain,(
% 1.53/0.56    ~r1_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) | spl8_5),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f104,f101,f39,f103,f42,f97,f97,f131,f46])).
% 1.53/0.56  fof(f46,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f21])).
% 1.53/0.56  fof(f131,plain,(
% 1.53/0.56    ~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) | spl8_5),
% 1.53/0.56    inference(avatar_component_clause,[],[f129])).
% 1.53/0.56  fof(f129,plain,(
% 1.53/0.56    spl8_5 <=> r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.53/0.56  fof(f142,plain,(
% 1.53/0.56    ( ! [X0] : (r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0))) )),
% 1.53/0.56    inference(superposition,[],[f137,f98])).
% 1.53/0.56  fof(f98,plain,(
% 1.53/0.56    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))) )),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f40,f41,f39,f42,f54])).
% 1.53/0.56  fof(f54,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f27])).
% 1.53/0.56  fof(f27,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.53/0.56    inference(flattening,[],[f26])).
% 1.53/0.56  fof(f26,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f10])).
% 1.53/0.56  fof(f10,axiom,(
% 1.53/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).
% 1.53/0.56  fof(f137,plain,(
% 1.53/0.56    ( ! [X0] : (r3_lattice3(sK0,k16_lattice3(sK0,X0),X0)) )),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f40,f41,f42,f39,f96,f76])).
% 1.53/0.56  fof(f76,plain,(
% 1.53/0.56    ( ! [X2,X0] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | r3_lattice3(X0,k16_lattice3(X0,X2),X2)) )),
% 1.53/0.56    inference(equality_resolution,[],[f52])).
% 1.53/0.56  fof(f52,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1) )),
% 1.53/0.56    inference(cnf_transformation,[],[f23])).
% 1.53/0.56  fof(f23,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.53/0.56    inference(flattening,[],[f22])).
% 1.53/0.56  fof(f22,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f9])).
% 1.53/0.56  fof(f9,axiom,(
% 1.53/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).
% 1.53/0.56  fof(f96,plain,(
% 1.53/0.56    ( ! [X0] : (m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f39,f42,f43])).
% 1.53/0.56  fof(f43,plain,(
% 1.53/0.56    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f17])).
% 1.53/0.56  fof(f17,plain,(
% 1.53/0.56    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.53/0.56    inference(flattening,[],[f16])).
% 1.53/0.56  fof(f16,plain,(
% 1.53/0.56    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f7])).
% 1.53/0.56  fof(f7,axiom,(
% 1.53/0.56    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 1.53/0.56  fof(f97,plain,(
% 1.53/0.56    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f39,f42,f53])).
% 1.53/0.57  fof(f53,plain,(
% 1.53/0.57    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f25])).
% 1.53/0.57  fof(f25,plain,(
% 1.53/0.57    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.53/0.57    inference(flattening,[],[f24])).
% 1.53/0.57  fof(f24,plain,(
% 1.53/0.57    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f6])).
% 1.53/0.57  fof(f6,axiom,(
% 1.53/0.57    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 1.53/0.57  fof(f103,plain,(
% 1.53/0.57    v8_lattices(sK0)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f40,f39,f42,f70])).
% 1.53/0.57  fof(f70,plain,(
% 1.53/0.57    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f34])).
% 1.53/0.57  fof(f34,plain,(
% 1.53/0.57    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.53/0.57    inference(flattening,[],[f33])).
% 1.53/0.57  fof(f33,plain,(
% 1.53/0.57    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f2])).
% 1.53/0.57  fof(f2,axiom,(
% 1.53/0.57    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 1.53/0.57  fof(f104,plain,(
% 1.53/0.57    v9_lattices(sK0)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f40,f39,f42,f71])).
% 1.53/0.57  fof(f71,plain,(
% 1.53/0.57    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v9_lattices(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f34])).
% 1.53/0.57  fof(f101,plain,(
% 1.53/0.57    v6_lattices(sK0)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f40,f39,f42,f68])).
% 1.53/0.57  fof(f68,plain,(
% 1.53/0.57    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f34])).
% 1.53/0.57  fof(f195,plain,(
% 1.53/0.57    m1_subset_1(sK6(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | spl8_5),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f42,f39,f97,f193,f63])).
% 1.53/0.57  fof(f63,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r4_lattice3(X0,X1,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f32])).
% 1.53/0.57  fof(f199,plain,(
% 1.53/0.57    r2_hidden(sK6(sK0,k15_lattice3(sK0,sK2),sK1),sK2) | spl8_5),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f38,f196,f55])).
% 1.53/0.57  fof(f55,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f28])).
% 1.53/0.57  fof(f28,plain,(
% 1.53/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f1])).
% 1.53/0.57  fof(f1,axiom,(
% 1.53/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.53/0.57  fof(f196,plain,(
% 1.53/0.57    r2_hidden(sK6(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | spl8_5),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f39,f42,f97,f193,f64])).
% 1.53/0.57  fof(f64,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(sK6(X0,X1,X2),X2) | r4_lattice3(X0,X1,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f32])).
% 1.53/0.57  fof(f38,plain,(
% 1.53/0.57    r1_tarski(sK1,sK2)),
% 1.53/0.57    inference(cnf_transformation,[],[f15])).
% 1.53/0.57  fof(f15,plain,(
% 1.53/0.57    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.53/0.57    inference(flattening,[],[f14])).
% 1.53/0.57  fof(f14,plain,(
% 1.53/0.57    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,negated_conjecture,(
% 1.53/0.57    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 1.53/0.57    inference(negated_conjecture,[],[f12])).
% 1.53/0.57  fof(f12,conjecture,(
% 1.53/0.57    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).
% 1.53/0.57  fof(f42,plain,(
% 1.53/0.57    l3_lattices(sK0)),
% 1.53/0.57    inference(cnf_transformation,[],[f15])).
% 1.53/0.57  fof(f40,plain,(
% 1.53/0.57    v10_lattices(sK0)),
% 1.53/0.57    inference(cnf_transformation,[],[f15])).
% 1.53/0.57  fof(f39,plain,(
% 1.53/0.57    ~v2_struct_0(sK0)),
% 1.53/0.57    inference(cnf_transformation,[],[f15])).
% 1.53/0.57  fof(f41,plain,(
% 1.53/0.57    v4_lattice3(sK0)),
% 1.53/0.57    inference(cnf_transformation,[],[f15])).
% 1.53/0.57  fof(f181,plain,(
% 1.53/0.57    spl8_4),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f179])).
% 1.53/0.57  fof(f179,plain,(
% 1.53/0.57    $false | spl8_4),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f42,f39,f137,f96,f159,f146,f148,f58])).
% 1.53/0.57  fof(f148,plain,(
% 1.53/0.57    ~r1_lattices(sK0,k16_lattice3(sK0,sK2),sK5(sK0,k16_lattice3(sK0,sK2),sK1)) | spl8_4),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f39,f42,f96,f140,f61])).
% 1.53/0.57  fof(f61,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_lattices(X0,X1,sK5(X0,X1,X2)) | r3_lattice3(X0,X1,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f30])).
% 1.53/0.57  fof(f140,plain,(
% 1.53/0.57    ~r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1) | spl8_4),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f41,f42,f39,f40,f96,f96,f127,f77])).
% 1.53/0.57  fof(f77,plain,(
% 1.53/0.57    ( ! [X2,X0,X3] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X3,X2) | r3_lattices(X0,X3,k16_lattice3(X0,X2))) )),
% 1.53/0.57    inference(equality_resolution,[],[f51])).
% 1.53/0.57  fof(f51,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X3,X2) | r3_lattices(X0,X3,X1) | k16_lattice3(X0,X2) != X1) )),
% 1.53/0.57    inference(cnf_transformation,[],[f23])).
% 1.53/0.57  fof(f127,plain,(
% 1.53/0.57    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1)) | spl8_4),
% 1.53/0.57    inference(avatar_component_clause,[],[f125])).
% 1.53/0.57  fof(f125,plain,(
% 1.53/0.57    spl8_4 <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.53/0.57  fof(f146,plain,(
% 1.53/0.57    m1_subset_1(sK5(sK0,k16_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | spl8_4),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f42,f39,f96,f140,f59])).
% 1.53/0.57  fof(f59,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r3_lattice3(X0,X1,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f30])).
% 1.53/0.57  fof(f159,plain,(
% 1.53/0.57    r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),sK2) | spl8_4),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f38,f147,f55])).
% 1.53/0.57  fof(f147,plain,(
% 1.53/0.57    r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),sK1) | spl8_4),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f39,f42,f96,f140,f60])).
% 1.53/0.57  fof(f60,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(sK5(X0,X1,X2),X2) | r3_lattice3(X0,X1,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f30])).
% 1.53/0.57  fof(f132,plain,(
% 1.53/0.57    ~spl8_4 | ~spl8_5),
% 1.53/0.57    inference(avatar_split_clause,[],[f37,f129,f125])).
% 1.53/0.57  fof(f37,plain,(
% 1.53/0.57    ~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) | ~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1))),
% 1.53/0.57    inference(cnf_transformation,[],[f15])).
% 1.53/0.57  % SZS output end Proof for theBenchmark
% 1.53/0.57  % (30940)------------------------------
% 1.53/0.57  % (30940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (30940)Termination reason: Refutation
% 1.53/0.57  
% 1.53/0.57  % (30940)Memory used [KB]: 6396
% 1.53/0.57  % (30940)Time elapsed: 0.121 s
% 1.53/0.57  % (30940)------------------------------
% 1.53/0.57  % (30940)------------------------------
% 1.53/0.57  % (30958)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.53/0.57  % (30935)Success in time 0.204 s
%------------------------------------------------------------------------------
