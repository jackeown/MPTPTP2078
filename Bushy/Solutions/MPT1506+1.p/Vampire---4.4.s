%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattice3__t40_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:54 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 127 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  264 ( 496 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f97,f104,f111,f118,f125,f132,f139,f158,f188,f209])).

fof(f209,plain,
    ( spl7_1
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | spl7_21 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f207,f89])).

fof(f89,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f207,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f206,f117])).

fof(f117,plain,
    ( r3_lattice3(sK0,sK1,sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_8
  <=> r3_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f206,plain,
    ( ~ r3_lattice3(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f205,f124])).

fof(f124,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_10
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f205,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_lattice3(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f203,f110])).

fof(f110,plain,
    ( l3_lattices(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl7_6
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f203,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_lattice3(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl7_21 ),
    inference(resolution,[],[f187,f82])).

fof(f82,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r3_lattice3(X1,X3,X2)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | ~ r3_lattice3(X1,X3,X2)
      | r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t40_lattice3.p',fraenkel_a_2_1_lattice3)).

fof(f187,plain,
    ( ~ r2_hidden(sK1,a_2_1_lattice3(sK0,sK2))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl7_21
  <=> ~ r2_hidden(sK1,a_2_1_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f188,plain,
    ( ~ spl7_21
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | spl7_13 ),
    inference(avatar_split_clause,[],[f169,f130,f123,f109,f102,f95,f88,f186])).

fof(f95,plain,
    ( spl7_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f102,plain,
    ( spl7_4
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f130,plain,
    ( spl7_13
  <=> ~ r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f169,plain,
    ( ~ r2_hidden(sK1,a_2_1_lattice3(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f168,f124])).

fof(f168,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,a_2_1_lattice3(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(resolution,[],[f164,f131])).

fof(f131,plain,
    ( ~ r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X1,k16_lattice3(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_1_lattice3(sK0,X0)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f163,f89])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X1,k16_lattice3(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_1_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f162,f110])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X1,k16_lattice3(sK0,X0))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_1_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f161,f103])).

fof(f103,plain,
    ( v4_lattice3(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X1,k16_lattice3(sK0,X0))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_1_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f160,f96])).

fof(f96,plain,
    ( v10_lattices(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X1,k16_lattice3(sK0,X0))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_1_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(superposition,[],[f63,f143])).

fof(f143,plain,
    ( ! [X0] : k16_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_1_lattice3(sK0,X0))
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f141,f89])).

fof(f141,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | k16_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_1_lattice3(sK0,X0)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f66,f110])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t40_lattice3.p',d22_lattice3)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattice3__t40_lattice3.p',t38_lattice3)).

fof(f158,plain,
    ( spl7_16
    | spl7_18
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f142,f137,f156,f150])).

fof(f150,plain,
    ( spl7_16
  <=> ! [X1] : k16_lattice3(sK6,X1) = k15_lattice3(sK6,a_2_1_lattice3(sK6,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f156,plain,
    ( spl7_18
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f137,plain,
    ( spl7_14
  <=> l3_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f142,plain,
    ( ! [X1] :
        ( v2_struct_0(sK6)
        | k16_lattice3(sK6,X1) = k15_lattice3(sK6,a_2_1_lattice3(sK6,X1)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f66,f138])).

fof(f138,plain,
    ( l3_lattices(sK6)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f139,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f79,f137])).

fof(f79,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t40_lattice3.p',existence_l3_lattices)).

fof(f132,plain,(
    ~ spl7_13 ),
    inference(avatar_split_clause,[],[f54,f130])).

fof(f54,plain,(
    ~ r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( r3_lattice3(X0,X1,X2)
               => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/lattice3__t40_lattice3.p',t40_lattice3)).

fof(f125,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f55,f123])).

fof(f55,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f118,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f53,f116])).

fof(f53,plain,(
    r3_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f111,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f59,f109])).

fof(f59,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f104,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f58,f102])).

fof(f58,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f97,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f57,f95])).

fof(f57,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f56,f88])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
