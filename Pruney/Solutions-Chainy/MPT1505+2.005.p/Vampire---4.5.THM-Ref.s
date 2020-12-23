%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:41 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 320 expanded)
%              Number of leaves         :   21 (  96 expanded)
%              Depth                    :   23
%              Number of atoms          :  724 (1377 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f121,f131,f199,f204,f209,f214,f243,f261])).

fof(f261,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_8
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f259,f91])).

% (2873)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f91,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_5
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f259,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6
    | spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f257,f120])).

fof(f120,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f257,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,sK2)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_8
    | ~ spl7_9 ),
    inference(resolution,[],[f220,f130])).

fof(f130,plain,
    ( ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl7_8
  <=> r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f220,plain,
    ( ! [X2,X3] :
        ( r3_lattices(sK0,X2,k15_lattice3(sK0,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,X3) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f217,f143])).

fof(f143,plain,
    ( ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(superposition,[],[f122,f142])).

fof(f142,plain,
    ( ! [X8] : k15_lattice3(sK0,X8) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X8))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f116,f86])).

fof(f86,plain,
    ( l3_lattices(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f116,plain,
    ( ! [X8] :
        ( ~ l3_lattices(sK0)
        | k15_lattice3(sK0,X8) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X8)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f115,f71])).

fof(f71,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f115,plain,
    ( ! [X8] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | k15_lattice3(sK0,X8) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X8)) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f106,f76])).

fof(f76,plain,
    ( v10_lattices(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl7_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f106,plain,
    ( ! [X8] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | k15_lattice3(sK0,X8) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X8)) )
    | ~ spl7_3 ),
    inference(resolution,[],[f81,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

fof(f81,plain,
    ( v4_lattice3(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f122,plain,
    ( ! [X14] : m1_subset_1(k16_lattice3(sK0,X14),u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f99,f86])).

fof(f99,plain,
    ( ! [X14] :
        ( ~ l3_lattices(sK0)
        | m1_subset_1(k16_lattice3(sK0,X14),u1_struct_0(sK0)) )
    | spl7_1 ),
    inference(resolution,[],[f71,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f217,plain,
    ( ! [X2,X3] :
        ( r3_lattices(sK0,X2,k15_lattice3(sK0,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))
        | ~ r2_hidden(X2,X3) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,
    ( ! [X2,X3] :
        ( r3_lattices(sK0,X2,k15_lattice3(sK0,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))
        | ~ r2_hidden(X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(resolution,[],[f186,f180])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f179,f143])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f178,f165])).

fof(f165,plain,
    ( ! [X2] : r4_lattice3(sK0,k15_lattice3(sK0,X2),X2)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f164,f71])).

fof(f164,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | r4_lattice3(sK0,k15_lattice3(sK0,X2),X2) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f163,f86])).

fof(f163,plain,
    ( ! [X2] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | r4_lattice3(sK0,k15_lattice3(sK0,X2),X2) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f162,f81])).

fof(f162,plain,
    ( ! [X2] :
        ( ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | r4_lattice3(sK0,k15_lattice3(sK0,X2),X2) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f157,f76])).

fof(f157,plain,
    ( ! [X2] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | r4_lattice3(sK0,k15_lattice3(sK0,X2),X2) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f143,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | r4_lattice3(X0,k15_lattice3(X0,X1),X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

fof(f178,plain,
    ( ! [X8,X7,X9] :
        ( ~ r4_lattice3(sK0,X7,X9)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r2_hidden(X8,X9)
        | r1_lattices(sK0,X8,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f96,f86])).

fof(f96,plain,
    ( ! [X8,X7,X9] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r2_hidden(X8,X9)
        | r1_lattices(sK0,X8,X7)
        | ~ r4_lattice3(sK0,X7,X9) )
    | spl7_1 ),
    inference(resolution,[],[f71,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | r1_lattices(X0,X3,X1)
      | ~ r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f186,plain,
    ( ! [X15,X16] :
        ( ~ r1_lattices(sK0,X15,X16)
        | r3_lattices(sK0,X15,X16)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0)) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl7_9
  <=> ! [X16,X15] :
        ( ~ m1_subset_1(X15,u1_struct_0(sK0))
        | r3_lattices(sK0,X15,X16)
        | ~ r1_lattices(sK0,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f243,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f241,f91])).

fof(f241,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6
    | spl7_7
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f237,f120])).

fof(f237,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,sK2)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_7
    | ~ spl7_9 ),
    inference(resolution,[],[f219,f126])).

fof(f126,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl7_7
  <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,k16_lattice3(sK0,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f218,f122])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,k16_lattice3(sK0,X0),X1)
        | ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,k16_lattice3(sK0,X0),X1)
        | ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(resolution,[],[f186,f173])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k16_lattice3(sK0,X1),X0)
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f171,f122])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | r1_lattices(sK0,k16_lattice3(sK0,X1),X0)
        | ~ m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f169,f141])).

fof(f141,plain,
    ( ! [X2] : r3_lattice3(sK0,k16_lattice3(sK0,X2),X2)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f140,f71])).

fof(f140,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f139,f86])).

fof(f139,plain,
    ( ! [X2] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f138,f81])).

fof(f138,plain,
    ( ! [X2] :
        ( ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f133,f76])).

fof(f133,plain,
    ( ! [X2] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2) )
    | spl7_1
    | ~ spl7_4 ),
    inference(resolution,[],[f122,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | r3_lattice3(X0,k16_lattice3(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(f169,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f93,f86])).

fof(f93,plain,
    ( ! [X2,X0,X1] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | r1_lattices(sK0,X0,X1)
        | ~ r3_lattice3(sK0,X0,X2) )
    | spl7_1 ),
    inference(resolution,[],[f71,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | r1_lattices(X0,X1,X3)
      | ~ r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f214,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_12 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f212,f86])).

fof(f212,plain,
    ( ~ l3_lattices(sK0)
    | spl7_1
    | ~ spl7_2
    | spl7_12 ),
    inference(subsumption_resolution,[],[f211,f76])).

fof(f211,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl7_1
    | spl7_12 ),
    inference(subsumption_resolution,[],[f210,f71])).

fof(f210,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl7_12 ),
    inference(resolution,[],[f198,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f198,plain,
    ( ~ v6_lattices(sK0)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl7_12
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f209,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_11 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_11 ),
    inference(subsumption_resolution,[],[f207,f86])).

fof(f207,plain,
    ( ~ l3_lattices(sK0)
    | spl7_1
    | ~ spl7_2
    | spl7_11 ),
    inference(subsumption_resolution,[],[f206,f76])).

fof(f206,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl7_1
    | spl7_11 ),
    inference(subsumption_resolution,[],[f205,f71])).

fof(f205,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl7_11 ),
    inference(resolution,[],[f194,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f194,plain,
    ( ~ v8_lattices(sK0)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl7_11
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f204,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_10 ),
    inference(subsumption_resolution,[],[f202,f86])).

fof(f202,plain,
    ( ~ l3_lattices(sK0)
    | spl7_1
    | ~ spl7_2
    | spl7_10 ),
    inference(subsumption_resolution,[],[f201,f76])).

fof(f201,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl7_1
    | spl7_10 ),
    inference(subsumption_resolution,[],[f200,f71])).

fof(f200,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl7_10 ),
    inference(resolution,[],[f190,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f190,plain,
    ( ~ v9_lattices(sK0)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl7_10
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f199,plain,
    ( spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f183,f84,f69,f196,f192,f188,f185])).

fof(f183,plain,
    ( ! [X15,X16] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X15,X16)
        | r3_lattices(sK0,X15,X16) )
    | spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f100,f86])).

fof(f100,plain,
    ( ! [X15,X16] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X15,X16)
        | r3_lattices(sK0,X15,X16) )
    | spl7_1 ),
    inference(resolution,[],[f71,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f131,plain,
    ( ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f29,f128,f124])).

fof(f29,plain,
    ( ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f121,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f31,f118])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f92,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f30,f89])).

fof(f30,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f87,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f35,f84])).

fof(f35,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f34,f79])).

fof(f34,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f77,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f33,f74])).

fof(f33,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (1209401344)
% 0.13/0.36  ipcrm: permission denied for id (1212678145)
% 0.13/0.36  ipcrm: permission denied for id (1209434114)
% 0.13/0.36  ipcrm: permission denied for id (1209466883)
% 0.13/0.36  ipcrm: permission denied for id (1217134596)
% 0.13/0.36  ipcrm: permission denied for id (1209532422)
% 0.13/0.36  ipcrm: permission denied for id (1209565191)
% 0.13/0.36  ipcrm: permission denied for id (1215299592)
% 0.13/0.37  ipcrm: permission denied for id (1215365130)
% 0.13/0.37  ipcrm: permission denied for id (1209663499)
% 0.13/0.37  ipcrm: permission denied for id (1215430669)
% 0.13/0.37  ipcrm: permission denied for id (1212973070)
% 0.13/0.37  ipcrm: permission denied for id (1209761807)
% 0.13/0.37  ipcrm: permission denied for id (1213005840)
% 0.13/0.37  ipcrm: permission denied for id (1215463441)
% 0.13/0.37  ipcrm: permission denied for id (1209892882)
% 0.13/0.37  ipcrm: permission denied for id (1209925651)
% 0.13/0.38  ipcrm: permission denied for id (1213071380)
% 0.13/0.38  ipcrm: permission denied for id (1215496213)
% 0.13/0.38  ipcrm: permission denied for id (1216675862)
% 0.13/0.38  ipcrm: permission denied for id (1215561751)
% 0.13/0.38  ipcrm: permission denied for id (1213202456)
% 0.13/0.38  ipcrm: permission denied for id (1213235225)
% 0.13/0.38  ipcrm: permission denied for id (1216708634)
% 0.13/0.38  ipcrm: permission denied for id (1217265691)
% 0.13/0.38  ipcrm: permission denied for id (1210089500)
% 0.13/0.38  ipcrm: permission denied for id (1216774173)
% 0.19/0.39  ipcrm: permission denied for id (1213366302)
% 0.19/0.39  ipcrm: permission denied for id (1213399071)
% 0.19/0.39  ipcrm: permission denied for id (1210155040)
% 0.19/0.39  ipcrm: permission denied for id (1216806945)
% 0.19/0.39  ipcrm: permission denied for id (1213464610)
% 0.19/0.39  ipcrm: permission denied for id (1210220579)
% 0.19/0.39  ipcrm: permission denied for id (1210253348)
% 0.19/0.39  ipcrm: permission denied for id (1215725605)
% 0.19/0.39  ipcrm: permission denied for id (1210286118)
% 0.19/0.39  ipcrm: permission denied for id (1213530151)
% 0.19/0.39  ipcrm: permission denied for id (1213562920)
% 0.19/0.40  ipcrm: permission denied for id (1213595689)
% 0.19/0.40  ipcrm: permission denied for id (1213628458)
% 0.19/0.40  ipcrm: permission denied for id (1210417195)
% 0.19/0.40  ipcrm: permission denied for id (1213661228)
% 0.19/0.40  ipcrm: permission denied for id (1215758381)
% 0.19/0.40  ipcrm: permission denied for id (1210515502)
% 0.19/0.40  ipcrm: permission denied for id (1210548271)
% 0.19/0.40  ipcrm: permission denied for id (1216839728)
% 0.19/0.40  ipcrm: permission denied for id (1217298481)
% 0.19/0.40  ipcrm: permission denied for id (1213792306)
% 0.19/0.41  ipcrm: permission denied for id (1210679347)
% 0.19/0.41  ipcrm: permission denied for id (1213825076)
% 0.19/0.41  ipcrm: permission denied for id (1210744885)
% 0.19/0.41  ipcrm: permission denied for id (1210777654)
% 0.19/0.41  ipcrm: permission denied for id (1210810423)
% 0.19/0.41  ipcrm: permission denied for id (1210843192)
% 0.19/0.41  ipcrm: permission denied for id (1213857849)
% 0.19/0.41  ipcrm: permission denied for id (1215856698)
% 0.19/0.41  ipcrm: permission denied for id (1215922235)
% 0.19/0.41  ipcrm: permission denied for id (1217560636)
% 0.19/0.41  ipcrm: permission denied for id (1215987773)
% 0.19/0.42  ipcrm: permission denied for id (1216938046)
% 0.19/0.42  ipcrm: permission denied for id (1211072575)
% 0.19/0.42  ipcrm: permission denied for id (1214087232)
% 0.19/0.42  ipcrm: permission denied for id (1211138113)
% 0.19/0.42  ipcrm: permission denied for id (1211170882)
% 0.19/0.42  ipcrm: permission denied for id (1216086083)
% 0.19/0.42  ipcrm: permission denied for id (1211269188)
% 0.19/0.42  ipcrm: permission denied for id (1214185541)
% 0.19/0.42  ipcrm: permission denied for id (1211301958)
% 0.19/0.42  ipcrm: permission denied for id (1211334727)
% 0.19/0.43  ipcrm: permission denied for id (1211367496)
% 0.19/0.43  ipcrm: permission denied for id (1214218313)
% 0.19/0.43  ipcrm: permission denied for id (1214251082)
% 0.19/0.43  ipcrm: permission denied for id (1211465803)
% 0.19/0.43  ipcrm: permission denied for id (1211498572)
% 0.19/0.43  ipcrm: permission denied for id (1211531341)
% 0.19/0.43  ipcrm: permission denied for id (1211564110)
% 0.19/0.43  ipcrm: permission denied for id (1211596879)
% 0.19/0.43  ipcrm: permission denied for id (1211629648)
% 0.19/0.43  ipcrm: permission denied for id (1211662417)
% 0.19/0.43  ipcrm: permission denied for id (1214283858)
% 0.19/0.44  ipcrm: permission denied for id (1211695187)
% 0.19/0.44  ipcrm: permission denied for id (1211727956)
% 0.19/0.44  ipcrm: permission denied for id (1217364053)
% 0.19/0.44  ipcrm: permission denied for id (1211760726)
% 0.19/0.44  ipcrm: permission denied for id (1216151639)
% 0.19/0.44  ipcrm: permission denied for id (1211826264)
% 0.19/0.44  ipcrm: permission denied for id (1214382169)
% 0.19/0.44  ipcrm: permission denied for id (1211859034)
% 0.19/0.44  ipcrm: permission denied for id (1214414939)
% 0.19/0.44  ipcrm: permission denied for id (1211891804)
% 0.19/0.45  ipcrm: permission denied for id (1217003613)
% 0.19/0.45  ipcrm: permission denied for id (1211957342)
% 0.19/0.45  ipcrm: permission denied for id (1214513248)
% 0.19/0.45  ipcrm: permission denied for id (1214546017)
% 0.19/0.45  ipcrm: permission denied for id (1216249954)
% 0.19/0.45  ipcrm: permission denied for id (1216282723)
% 0.19/0.45  ipcrm: permission denied for id (1216315492)
% 0.19/0.45  ipcrm: permission denied for id (1214677093)
% 0.19/0.45  ipcrm: permission denied for id (1214709862)
% 0.19/0.45  ipcrm: permission denied for id (1216381031)
% 0.19/0.46  ipcrm: permission denied for id (1214775400)
% 0.19/0.46  ipcrm: permission denied for id (1214808169)
% 0.19/0.46  ipcrm: permission denied for id (1212088426)
% 0.19/0.46  ipcrm: permission denied for id (1212121195)
% 0.19/0.46  ipcrm: permission denied for id (1212153964)
% 0.19/0.46  ipcrm: permission denied for id (1214840941)
% 0.19/0.46  ipcrm: permission denied for id (1214873710)
% 0.19/0.46  ipcrm: permission denied for id (1212219503)
% 0.19/0.46  ipcrm: permission denied for id (1215004785)
% 0.19/0.46  ipcrm: permission denied for id (1212317810)
% 0.19/0.47  ipcrm: permission denied for id (1212350579)
% 0.19/0.47  ipcrm: permission denied for id (1216446580)
% 0.19/0.47  ipcrm: permission denied for id (1215037557)
% 0.19/0.47  ipcrm: permission denied for id (1212416118)
% 0.19/0.47  ipcrm: permission denied for id (1212448887)
% 0.19/0.47  ipcrm: permission denied for id (1215070328)
% 0.19/0.47  ipcrm: permission denied for id (1217101945)
% 0.19/0.47  ipcrm: permission denied for id (1212514426)
% 0.19/0.47  ipcrm: permission denied for id (1212547195)
% 0.19/0.47  ipcrm: permission denied for id (1216512124)
% 0.19/0.48  ipcrm: permission denied for id (1215168637)
% 0.19/0.48  ipcrm: permission denied for id (1212612734)
% 0.19/0.48  ipcrm: permission denied for id (1215201407)
% 0.90/0.59  % (2870)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.90/0.59  % (2862)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.90/0.59  % (2859)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.90/0.59  % (2865)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.90/0.60  % (2862)Refutation found. Thanks to Tanya!
% 0.90/0.60  % SZS status Theorem for theBenchmark
% 0.90/0.60  % (2866)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.90/0.60  % SZS output start Proof for theBenchmark
% 0.90/0.60  fof(f262,plain,(
% 0.90/0.60    $false),
% 0.90/0.60    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f121,f131,f199,f204,f209,f214,f243,f261])).
% 0.90/0.60  fof(f261,plain,(
% 0.90/0.60    spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_8 | ~spl7_9),
% 0.90/0.60    inference(avatar_contradiction_clause,[],[f260])).
% 0.90/0.60  fof(f260,plain,(
% 0.90/0.60    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_8 | ~spl7_9)),
% 0.90/0.60    inference(subsumption_resolution,[],[f259,f91])).
% 0.90/0.60  % (2873)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.90/0.60  fof(f91,plain,(
% 0.90/0.60    r2_hidden(sK1,sK2) | ~spl7_5),
% 0.90/0.60    inference(avatar_component_clause,[],[f89])).
% 0.90/0.60  fof(f89,plain,(
% 0.90/0.60    spl7_5 <=> r2_hidden(sK1,sK2)),
% 0.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.90/0.60  fof(f259,plain,(
% 0.90/0.60    ~r2_hidden(sK1,sK2) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6 | spl7_8 | ~spl7_9)),
% 0.90/0.60    inference(subsumption_resolution,[],[f257,f120])).
% 0.90/0.60  fof(f120,plain,(
% 0.90/0.60    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl7_6),
% 0.90/0.60    inference(avatar_component_clause,[],[f118])).
% 0.90/0.60  fof(f118,plain,(
% 0.90/0.60    spl7_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.90/0.60  fof(f257,plain,(
% 0.90/0.60    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK2) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_8 | ~spl7_9)),
% 0.90/0.60    inference(resolution,[],[f220,f130])).
% 0.90/0.60  fof(f130,plain,(
% 0.90/0.60    ~r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | spl7_8),
% 0.90/0.60    inference(avatar_component_clause,[],[f128])).
% 0.90/0.60  fof(f128,plain,(
% 0.90/0.60    spl7_8 <=> r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2))),
% 0.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.90/0.60  fof(f220,plain,(
% 0.90/0.60    ( ! [X2,X3] : (r3_lattices(sK0,X2,k15_lattice3(sK0,X3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X3)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_9)),
% 0.90/0.60    inference(subsumption_resolution,[],[f217,f143])).
% 0.90/0.60  fof(f143,plain,(
% 0.90/0.60    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.90/0.60    inference(superposition,[],[f122,f142])).
% 0.90/0.60  fof(f142,plain,(
% 0.90/0.60    ( ! [X8] : (k15_lattice3(sK0,X8) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X8))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f116,f86])).
% 0.90/0.60  fof(f86,plain,(
% 0.90/0.60    l3_lattices(sK0) | ~spl7_4),
% 0.90/0.60    inference(avatar_component_clause,[],[f84])).
% 0.90/0.60  fof(f84,plain,(
% 0.90/0.60    spl7_4 <=> l3_lattices(sK0)),
% 0.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.90/0.60  fof(f116,plain,(
% 0.90/0.60    ( ! [X8] : (~l3_lattices(sK0) | k15_lattice3(sK0,X8) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X8))) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.90/0.60    inference(subsumption_resolution,[],[f115,f71])).
% 0.90/0.60  fof(f71,plain,(
% 0.90/0.60    ~v2_struct_0(sK0) | spl7_1),
% 0.90/0.60    inference(avatar_component_clause,[],[f69])).
% 0.90/0.60  fof(f69,plain,(
% 0.90/0.60    spl7_1 <=> v2_struct_0(sK0)),
% 0.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.90/0.60  fof(f115,plain,(
% 0.90/0.60    ( ! [X8] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | k15_lattice3(sK0,X8) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X8))) ) | (~spl7_2 | ~spl7_3)),
% 0.90/0.60    inference(subsumption_resolution,[],[f106,f76])).
% 0.90/0.60  fof(f76,plain,(
% 0.90/0.60    v10_lattices(sK0) | ~spl7_2),
% 0.90/0.60    inference(avatar_component_clause,[],[f74])).
% 0.90/0.60  fof(f74,plain,(
% 0.90/0.60    spl7_2 <=> v10_lattices(sK0)),
% 0.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.90/0.60  fof(f106,plain,(
% 0.90/0.60    ( ! [X8] : (~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | k15_lattice3(sK0,X8) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X8))) ) | ~spl7_3),
% 0.90/0.60    inference(resolution,[],[f81,f42])).
% 0.90/0.60  fof(f42,plain,(
% 0.90/0.60    ( ! [X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))) )),
% 0.90/0.60    inference(cnf_transformation,[],[f16])).
% 0.90/0.60  fof(f16,plain,(
% 0.90/0.60    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.90/0.60    inference(flattening,[],[f15])).
% 0.90/0.60  fof(f15,plain,(
% 0.90/0.60    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.90/0.60    inference(ennf_transformation,[],[f8])).
% 0.90/0.60  fof(f8,axiom,(
% 0.90/0.60    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 0.90/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).
% 0.90/0.60  fof(f81,plain,(
% 0.90/0.60    v4_lattice3(sK0) | ~spl7_3),
% 0.90/0.60    inference(avatar_component_clause,[],[f79])).
% 0.90/0.60  fof(f79,plain,(
% 0.90/0.60    spl7_3 <=> v4_lattice3(sK0)),
% 0.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.90/0.60  fof(f122,plain,(
% 0.90/0.60    ( ! [X14] : (m1_subset_1(k16_lattice3(sK0,X14),u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f99,f86])).
% 0.90/0.60  fof(f99,plain,(
% 0.90/0.60    ( ! [X14] : (~l3_lattices(sK0) | m1_subset_1(k16_lattice3(sK0,X14),u1_struct_0(sK0))) ) | spl7_1),
% 0.90/0.60    inference(resolution,[],[f71,f61])).
% 0.90/0.60  fof(f61,plain,(
% 0.90/0.60    ( ! [X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))) )),
% 0.90/0.60    inference(cnf_transformation,[],[f26])).
% 0.90/0.60  fof(f26,plain,(
% 0.90/0.60    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.90/0.60    inference(flattening,[],[f25])).
% 0.90/0.60  fof(f25,plain,(
% 0.90/0.60    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.90/0.60    inference(ennf_transformation,[],[f6])).
% 0.90/0.60  fof(f6,axiom,(
% 0.90/0.60    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.90/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 0.90/0.60  fof(f217,plain,(
% 0.90/0.60    ( ! [X2,X3] : (r3_lattices(sK0,X2,k15_lattice3(sK0,X3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0)) | ~r2_hidden(X2,X3)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_9)),
% 0.90/0.60    inference(duplicate_literal_removal,[],[f216])).
% 0.90/0.60  fof(f216,plain,(
% 0.90/0.60    ( ! [X2,X3] : (r3_lattices(sK0,X2,k15_lattice3(sK0,X3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0)) | ~r2_hidden(X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_9)),
% 0.90/0.60    inference(resolution,[],[f186,f180])).
% 0.90/0.60  fof(f180,plain,(
% 0.90/0.60    ( ! [X0,X1] : (r1_lattices(sK0,X0,k15_lattice3(sK0,X1)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f179,f143])).
% 0.90/0.60  fof(f179,plain,(
% 0.90/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | r1_lattices(sK0,X0,k15_lattice3(sK0,X1)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.90/0.60    inference(resolution,[],[f178,f165])).
% 0.90/0.60  fof(f165,plain,(
% 0.90/0.60    ( ! [X2] : (r4_lattice3(sK0,k15_lattice3(sK0,X2),X2)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f164,f71])).
% 0.90/0.60  fof(f164,plain,(
% 0.90/0.60    ( ! [X2] : (v2_struct_0(sK0) | r4_lattice3(sK0,k15_lattice3(sK0,X2),X2)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f163,f86])).
% 0.90/0.60  fof(f163,plain,(
% 0.90/0.60    ( ! [X2] : (~l3_lattices(sK0) | v2_struct_0(sK0) | r4_lattice3(sK0,k15_lattice3(sK0,X2),X2)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f162,f81])).
% 0.90/0.60  fof(f162,plain,(
% 0.90/0.60    ( ! [X2] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | r4_lattice3(sK0,k15_lattice3(sK0,X2),X2)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f157,f76])).
% 0.90/0.60  fof(f157,plain,(
% 0.90/0.60    ( ! [X2] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | r4_lattice3(sK0,k15_lattice3(sK0,X2),X2)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.90/0.60    inference(resolution,[],[f143,f66])).
% 0.90/0.60  fof(f66,plain,(
% 0.90/0.60    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | r4_lattice3(X0,k15_lattice3(X0,X1),X1)) )),
% 0.90/0.60    inference(equality_resolution,[],[f52])).
% 0.90/0.60  fof(f52,plain,(
% 0.90/0.60    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2) )),
% 0.90/0.60    inference(cnf_transformation,[],[f20])).
% 0.90/0.60  fof(f20,plain,(
% 0.90/0.60    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.90/0.60    inference(flattening,[],[f19])).
% 0.90/0.60  fof(f19,plain,(
% 0.90/0.60    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.90/0.60    inference(ennf_transformation,[],[f5])).
% 0.90/0.60  fof(f5,axiom,(
% 0.90/0.60    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 0.90/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 0.90/0.60  fof(f178,plain,(
% 0.90/0.60    ( ! [X8,X7,X9] : (~r4_lattice3(sK0,X7,X9) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r2_hidden(X8,X9) | r1_lattices(sK0,X8,X7) | ~m1_subset_1(X7,u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f96,f86])).
% 0.90/0.60  fof(f96,plain,(
% 0.90/0.60    ( ! [X8,X7,X9] : (~l3_lattices(sK0) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r2_hidden(X8,X9) | r1_lattices(sK0,X8,X7) | ~r4_lattice3(sK0,X7,X9)) ) | spl7_1),
% 0.90/0.60    inference(resolution,[],[f71,f57])).
% 0.90/0.60  fof(f57,plain,(
% 0.90/0.60    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X2) | r1_lattices(X0,X3,X1) | ~r4_lattice3(X0,X1,X2)) )),
% 0.90/0.60    inference(cnf_transformation,[],[f24])).
% 0.90/0.60  fof(f24,plain,(
% 0.90/0.60    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.90/0.60    inference(flattening,[],[f23])).
% 0.90/0.60  fof(f23,plain,(
% 0.90/0.60    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.90/0.60    inference(ennf_transformation,[],[f4])).
% 0.90/0.60  fof(f4,axiom,(
% 0.90/0.60    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.90/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 0.90/0.60  fof(f186,plain,(
% 0.90/0.60    ( ! [X15,X16] : (~r1_lattices(sK0,X15,X16) | r3_lattices(sK0,X15,X16) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0))) ) | ~spl7_9),
% 0.90/0.60    inference(avatar_component_clause,[],[f185])).
% 0.90/0.60  fof(f185,plain,(
% 0.90/0.60    spl7_9 <=> ! [X16,X15] : (~m1_subset_1(X15,u1_struct_0(sK0)) | r3_lattices(sK0,X15,X16) | ~r1_lattices(sK0,X15,X16) | ~m1_subset_1(X16,u1_struct_0(sK0)))),
% 0.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.90/0.60  fof(f243,plain,(
% 0.90/0.60    spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_9),
% 0.90/0.60    inference(avatar_contradiction_clause,[],[f242])).
% 0.90/0.60  fof(f242,plain,(
% 0.90/0.60    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_9)),
% 0.90/0.60    inference(subsumption_resolution,[],[f241,f91])).
% 0.90/0.60  fof(f241,plain,(
% 0.90/0.60    ~r2_hidden(sK1,sK2) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6 | spl7_7 | ~spl7_9)),
% 0.90/0.60    inference(subsumption_resolution,[],[f237,f120])).
% 0.90/0.60  fof(f237,plain,(
% 0.90/0.60    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK2) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_7 | ~spl7_9)),
% 0.90/0.60    inference(resolution,[],[f219,f126])).
% 0.90/0.60  fof(f126,plain,(
% 0.90/0.60    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | spl7_7),
% 0.90/0.60    inference(avatar_component_clause,[],[f124])).
% 0.90/0.60  fof(f124,plain,(
% 0.90/0.60    spl7_7 <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.90/0.60  fof(f219,plain,(
% 0.90/0.60    ( ! [X0,X1] : (r3_lattices(sK0,k16_lattice3(sK0,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_9)),
% 0.90/0.60    inference(subsumption_resolution,[],[f218,f122])).
% 0.90/0.60  fof(f218,plain,(
% 0.90/0.60    ( ! [X0,X1] : (r3_lattices(sK0,k16_lattice3(sK0,X0),X1) | ~m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_9)),
% 0.90/0.60    inference(duplicate_literal_removal,[],[f215])).
% 0.90/0.60  fof(f215,plain,(
% 0.90/0.60    ( ! [X0,X1] : (r3_lattices(sK0,k16_lattice3(sK0,X0),X1) | ~m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_9)),
% 0.90/0.60    inference(resolution,[],[f186,f173])).
% 0.90/0.60  fof(f173,plain,(
% 0.90/0.60    ( ! [X0,X1] : (r1_lattices(sK0,k16_lattice3(sK0,X1),X0) | ~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f171,f122])).
% 0.90/0.60  fof(f171,plain,(
% 0.90/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | r1_lattices(sK0,k16_lattice3(sK0,X1),X0) | ~m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.90/0.60    inference(resolution,[],[f169,f141])).
% 0.90/0.60  fof(f141,plain,(
% 0.90/0.60    ( ! [X2] : (r3_lattice3(sK0,k16_lattice3(sK0,X2),X2)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f140,f71])).
% 0.90/0.60  fof(f140,plain,(
% 0.90/0.60    ( ! [X2] : (v2_struct_0(sK0) | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f139,f86])).
% 0.90/0.60  fof(f139,plain,(
% 0.90/0.60    ( ! [X2] : (~l3_lattices(sK0) | v2_struct_0(sK0) | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f138,f81])).
% 0.90/0.60  fof(f138,plain,(
% 0.90/0.60    ( ! [X2] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2)) ) | (spl7_1 | ~spl7_2 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f133,f76])).
% 0.90/0.60  fof(f133,plain,(
% 0.90/0.60    ( ! [X2] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2)) ) | (spl7_1 | ~spl7_4)),
% 0.90/0.60    inference(resolution,[],[f122,f64])).
% 0.90/0.60  fof(f64,plain,(
% 0.90/0.60    ( ! [X2,X0] : (~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | r3_lattice3(X0,k16_lattice3(X0,X2),X2)) )),
% 0.90/0.60    inference(equality_resolution,[],[f47])).
% 0.90/0.60  fof(f47,plain,(
% 0.90/0.60    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1) )),
% 0.90/0.60    inference(cnf_transformation,[],[f18])).
% 0.90/0.60  fof(f18,plain,(
% 0.90/0.60    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.90/0.60    inference(flattening,[],[f17])).
% 0.90/0.60  fof(f17,plain,(
% 0.90/0.60    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.90/0.60    inference(ennf_transformation,[],[f7])).
% 0.90/0.60  fof(f7,axiom,(
% 0.90/0.60    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 0.90/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).
% 0.90/0.60  fof(f169,plain,(
% 0.90/0.60    ( ! [X2,X0,X1] : (~r3_lattice3(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | r1_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f93,f86])).
% 0.90/0.60  fof(f93,plain,(
% 0.90/0.60    ( ! [X2,X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | r1_lattices(sK0,X0,X1) | ~r3_lattice3(sK0,X0,X2)) ) | spl7_1),
% 0.90/0.60    inference(resolution,[],[f71,f53])).
% 0.90/0.60  fof(f53,plain,(
% 0.90/0.60    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X2) | r1_lattices(X0,X1,X3) | ~r3_lattice3(X0,X1,X2)) )),
% 0.90/0.60    inference(cnf_transformation,[],[f22])).
% 0.90/0.60  fof(f22,plain,(
% 0.90/0.60    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.90/0.60    inference(flattening,[],[f21])).
% 0.90/0.60  fof(f21,plain,(
% 0.90/0.60    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.90/0.60    inference(ennf_transformation,[],[f3])).
% 0.90/0.60  fof(f3,axiom,(
% 0.90/0.60    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 0.90/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 0.90/0.60  fof(f214,plain,(
% 0.90/0.60    spl7_1 | ~spl7_2 | ~spl7_4 | spl7_12),
% 0.90/0.60    inference(avatar_contradiction_clause,[],[f213])).
% 0.90/0.60  fof(f213,plain,(
% 0.90/0.60    $false | (spl7_1 | ~spl7_2 | ~spl7_4 | spl7_12)),
% 0.90/0.60    inference(subsumption_resolution,[],[f212,f86])).
% 0.90/0.60  fof(f212,plain,(
% 0.90/0.60    ~l3_lattices(sK0) | (spl7_1 | ~spl7_2 | spl7_12)),
% 0.90/0.60    inference(subsumption_resolution,[],[f211,f76])).
% 0.90/0.60  fof(f211,plain,(
% 0.90/0.60    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl7_1 | spl7_12)),
% 0.90/0.60    inference(subsumption_resolution,[],[f210,f71])).
% 0.90/0.60  fof(f210,plain,(
% 0.90/0.60    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl7_12),
% 0.90/0.60    inference(resolution,[],[f198,f38])).
% 0.90/0.60  fof(f38,plain,(
% 0.90/0.60    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.90/0.60    inference(cnf_transformation,[],[f14])).
% 0.90/0.60  fof(f14,plain,(
% 0.90/0.60    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.90/0.60    inference(flattening,[],[f13])).
% 0.90/0.60  fof(f13,plain,(
% 0.90/0.60    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.90/0.60    inference(ennf_transformation,[],[f1])).
% 0.90/0.60  fof(f1,axiom,(
% 0.90/0.60    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.90/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.90/0.60  fof(f198,plain,(
% 0.90/0.60    ~v6_lattices(sK0) | spl7_12),
% 0.90/0.60    inference(avatar_component_clause,[],[f196])).
% 0.90/0.60  fof(f196,plain,(
% 0.90/0.60    spl7_12 <=> v6_lattices(sK0)),
% 0.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.90/0.60  fof(f209,plain,(
% 0.90/0.60    spl7_1 | ~spl7_2 | ~spl7_4 | spl7_11),
% 0.90/0.60    inference(avatar_contradiction_clause,[],[f208])).
% 0.90/0.60  fof(f208,plain,(
% 0.90/0.60    $false | (spl7_1 | ~spl7_2 | ~spl7_4 | spl7_11)),
% 0.90/0.60    inference(subsumption_resolution,[],[f207,f86])).
% 0.90/0.60  fof(f207,plain,(
% 0.90/0.60    ~l3_lattices(sK0) | (spl7_1 | ~spl7_2 | spl7_11)),
% 0.90/0.60    inference(subsumption_resolution,[],[f206,f76])).
% 0.90/0.60  fof(f206,plain,(
% 0.90/0.60    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl7_1 | spl7_11)),
% 0.90/0.60    inference(subsumption_resolution,[],[f205,f71])).
% 0.90/0.60  fof(f205,plain,(
% 0.90/0.60    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl7_11),
% 0.90/0.60    inference(resolution,[],[f194,f40])).
% 0.90/0.60  fof(f40,plain,(
% 0.90/0.60    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.90/0.60    inference(cnf_transformation,[],[f14])).
% 0.90/0.60  fof(f194,plain,(
% 0.90/0.60    ~v8_lattices(sK0) | spl7_11),
% 0.90/0.60    inference(avatar_component_clause,[],[f192])).
% 0.90/0.60  fof(f192,plain,(
% 0.90/0.60    spl7_11 <=> v8_lattices(sK0)),
% 0.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.90/0.60  fof(f204,plain,(
% 0.90/0.60    spl7_1 | ~spl7_2 | ~spl7_4 | spl7_10),
% 0.90/0.60    inference(avatar_contradiction_clause,[],[f203])).
% 0.90/0.60  fof(f203,plain,(
% 0.90/0.60    $false | (spl7_1 | ~spl7_2 | ~spl7_4 | spl7_10)),
% 0.90/0.60    inference(subsumption_resolution,[],[f202,f86])).
% 0.90/0.60  fof(f202,plain,(
% 0.90/0.60    ~l3_lattices(sK0) | (spl7_1 | ~spl7_2 | spl7_10)),
% 0.90/0.60    inference(subsumption_resolution,[],[f201,f76])).
% 0.90/0.60  fof(f201,plain,(
% 0.90/0.60    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl7_1 | spl7_10)),
% 0.90/0.60    inference(subsumption_resolution,[],[f200,f71])).
% 0.90/0.60  fof(f200,plain,(
% 0.90/0.60    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl7_10),
% 0.90/0.60    inference(resolution,[],[f190,f41])).
% 0.90/0.60  fof(f41,plain,(
% 0.90/0.60    ( ! [X0] : (v9_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.90/0.60    inference(cnf_transformation,[],[f14])).
% 0.90/0.60  fof(f190,plain,(
% 0.90/0.60    ~v9_lattices(sK0) | spl7_10),
% 0.90/0.60    inference(avatar_component_clause,[],[f188])).
% 0.90/0.60  fof(f188,plain,(
% 0.90/0.60    spl7_10 <=> v9_lattices(sK0)),
% 0.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.90/0.60  fof(f199,plain,(
% 0.90/0.60    spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | spl7_1 | ~spl7_4),
% 0.90/0.60    inference(avatar_split_clause,[],[f183,f84,f69,f196,f192,f188,f185])).
% 0.90/0.60  fof(f183,plain,(
% 0.90/0.60    ( ! [X15,X16] : (~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~r1_lattices(sK0,X15,X16) | r3_lattices(sK0,X15,X16)) ) | (spl7_1 | ~spl7_4)),
% 0.90/0.60    inference(subsumption_resolution,[],[f100,f86])).
% 0.90/0.60  fof(f100,plain,(
% 0.90/0.60    ( ! [X15,X16] : (~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~r1_lattices(sK0,X15,X16) | r3_lattices(sK0,X15,X16)) ) | spl7_1),
% 0.90/0.60    inference(resolution,[],[f71,f62])).
% 0.90/0.60  fof(f62,plain,(
% 0.90/0.60    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2)) )),
% 0.90/0.60    inference(cnf_transformation,[],[f28])).
% 0.90/0.60  fof(f28,plain,(
% 0.90/0.60    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.90/0.60    inference(flattening,[],[f27])).
% 0.90/0.60  fof(f27,plain,(
% 0.90/0.60    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.90/0.60    inference(ennf_transformation,[],[f2])).
% 0.90/0.60  fof(f2,axiom,(
% 0.90/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.90/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.90/0.60  fof(f131,plain,(
% 0.90/0.60    ~spl7_7 | ~spl7_8),
% 0.90/0.60    inference(avatar_split_clause,[],[f29,f128,f124])).
% 0.90/0.60  fof(f29,plain,(
% 0.90/0.60    ~r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | ~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.90/0.60    inference(cnf_transformation,[],[f12])).
% 0.90/0.60  fof(f12,plain,(
% 0.90/0.60    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.90/0.60    inference(flattening,[],[f11])).
% 0.90/0.60  fof(f11,plain,(
% 0.90/0.60    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.90/0.60    inference(ennf_transformation,[],[f10])).
% 0.90/0.60  fof(f10,negated_conjecture,(
% 0.90/0.60    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 0.90/0.60    inference(negated_conjecture,[],[f9])).
% 0.90/0.60  fof(f9,conjecture,(
% 0.90/0.60    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 0.90/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).
% 0.90/0.60  fof(f121,plain,(
% 0.90/0.60    spl7_6),
% 0.90/0.60    inference(avatar_split_clause,[],[f31,f118])).
% 0.90/0.60  fof(f31,plain,(
% 0.90/0.60    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.90/0.60    inference(cnf_transformation,[],[f12])).
% 0.90/0.60  fof(f92,plain,(
% 0.90/0.60    spl7_5),
% 0.90/0.60    inference(avatar_split_clause,[],[f30,f89])).
% 0.90/0.60  fof(f30,plain,(
% 0.90/0.60    r2_hidden(sK1,sK2)),
% 0.90/0.60    inference(cnf_transformation,[],[f12])).
% 0.90/0.60  fof(f87,plain,(
% 0.90/0.60    spl7_4),
% 0.90/0.60    inference(avatar_split_clause,[],[f35,f84])).
% 0.90/0.60  fof(f35,plain,(
% 0.90/0.60    l3_lattices(sK0)),
% 0.90/0.60    inference(cnf_transformation,[],[f12])).
% 0.90/0.60  fof(f82,plain,(
% 0.90/0.60    spl7_3),
% 0.90/0.60    inference(avatar_split_clause,[],[f34,f79])).
% 0.90/0.60  fof(f34,plain,(
% 0.90/0.60    v4_lattice3(sK0)),
% 0.90/0.60    inference(cnf_transformation,[],[f12])).
% 0.90/0.60  fof(f77,plain,(
% 0.90/0.60    spl7_2),
% 0.90/0.60    inference(avatar_split_clause,[],[f33,f74])).
% 0.90/0.60  fof(f33,plain,(
% 0.90/0.60    v10_lattices(sK0)),
% 0.90/0.60    inference(cnf_transformation,[],[f12])).
% 0.90/0.60  fof(f72,plain,(
% 0.90/0.60    ~spl7_1),
% 0.90/0.60    inference(avatar_split_clause,[],[f32,f69])).
% 0.90/0.60  fof(f32,plain,(
% 0.90/0.60    ~v2_struct_0(sK0)),
% 0.90/0.60    inference(cnf_transformation,[],[f12])).
% 0.90/0.60  % SZS output end Proof for theBenchmark
% 0.90/0.60  % (2862)------------------------------
% 0.90/0.60  % (2862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.90/0.60  % (2862)Termination reason: Refutation
% 0.90/0.60  
% 0.90/0.60  % (2862)Memory used [KB]: 10746
% 0.90/0.60  % (2862)Time elapsed: 0.063 s
% 0.90/0.60  % (2862)------------------------------
% 0.90/0.60  % (2862)------------------------------
% 0.90/0.60  % (2707)Success in time 0.252 s
%------------------------------------------------------------------------------
