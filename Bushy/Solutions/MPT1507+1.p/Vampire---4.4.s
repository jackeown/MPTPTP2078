%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattice3__t41_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:54 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 418 expanded)
%              Number of leaves         :   56 ( 153 expanded)
%              Depth                    :   21
%              Number of atoms          :  806 (1488 expanded)
%              Number of equality atoms :   36 (  83 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f568,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f111,f118,f125,f132,f139,f146,f153,f160,f170,f180,f187,f213,f220,f237,f244,f252,f275,f306,f313,f320,f326,f335,f336,f344,f351,f358,f363,f370,f373,f409,f481,f490,f497,f526,f566])).

fof(f566,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f564,f131])).

fof(f131,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl7_8
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f564,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f563,f152])).

fof(f152,plain,
    ( k15_lattice3(sK0,sK2) != sK1
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl7_15
  <=> k15_lattice3(sK0,sK2) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f563,plain,
    ( k15_lattice3(sK0,sK2) = sK1
    | ~ r2_hidden(sK1,sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f562,f110])).

fof(f110,plain,
    ( v10_lattices(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl7_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f562,plain,
    ( ~ v10_lattices(sK0)
    | k15_lattice3(sK0,sK2) = sK1
    | ~ r2_hidden(sK1,sK2)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f561,f103])).

fof(f103,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f561,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k15_lattice3(sK0,sK2) = sK1
    | ~ r2_hidden(sK1,sK2)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f560,f117])).

fof(f117,plain,
    ( v4_lattice3(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_4
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f560,plain,
    ( ~ v4_lattice3(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k15_lattice3(sK0,sK2) = sK1
    | ~ r2_hidden(sK1,sK2)
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f559,f145])).

fof(f145,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl7_12
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f559,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v4_lattice3(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k15_lattice3(sK0,sK2) = sK1
    | ~ r2_hidden(sK1,sK2)
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f554,f124])).

fof(f124,plain,
    ( l3_lattices(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_6
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f554,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v4_lattice3(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k15_lattice3(sK0,sK2) = sK1
    | ~ r2_hidden(sK1,sK2)
    | ~ spl7_10 ),
    inference(resolution,[],[f463,f138])).

fof(f138,plain,
    ( r4_lattice3(sK0,sK1,sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl7_10
  <=> r4_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f463,plain,(
    ! [X4,X5,X3] :
      ( ~ r4_lattice3(X3,X4,X5)
      | ~ l3_lattices(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ v4_lattice3(X3)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | k15_lattice3(X3,X5) = X4
      | ~ r2_hidden(X4,X5) ) ),
    inference(duplicate_literal_removal,[],[f460])).

fof(f460,plain,(
    ! [X4,X5,X3] :
      ( ~ v4_lattice3(X3)
      | ~ l3_lattices(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ r4_lattice3(X3,X4,X5)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | k15_lattice3(X3,X5) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f298,f285])).

fof(f285,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(subsumption_resolution,[],[f284,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',dt_k15_lattice3)).

fof(f284,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
      | r1_lattices(X0,X1,k15_lattice3(X0,X2))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(subsumption_resolution,[],[f283,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',cc1_lattices)).

fof(f283,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
      | r1_lattices(X0,X1,k15_lattice3(X0,X2))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(subsumption_resolution,[],[f282,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f282,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
      | r1_lattices(X0,X1,k15_lattice3(X0,X2))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(subsumption_resolution,[],[f281,f95])).

fof(f95,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f281,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
      | r1_lattices(X0,X1,k15_lattice3(X0,X2))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f276])).

fof(f276,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
      | r1_lattices(X0,X1,k15_lattice3(X0,X2))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f83,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',t38_lattice3)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',redefinition_r3_lattices)).

fof(f298,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,k15_lattice3(X0,X1))
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | k15_lattice3(X0,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f297,f75])).

fof(f297,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ r1_lattices(X0,X2,k15_lattice3(X0,X1))
      | k15_lattice3(X0,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f296,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f296,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ r1_lattices(X0,X2,k15_lattice3(X0,X1))
      | k15_lattice3(X0,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f295,f89])).

fof(f89,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',dt_l3_lattices)).

fof(f295,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ r1_lattices(X0,X2,k15_lattice3(X0,X1))
      | k15_lattice3(X0,X1) = X2 ) ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ r1_lattices(X0,X2,k15_lattice3(X0,X1))
      | v2_struct_0(X0)
      | k15_lattice3(X0,X1) = X2 ) ),
    inference(resolution,[],[f97,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',t26_lattices)).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X3)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,X2,X3)
      | k15_lattice3(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',d21_lattice3)).

fof(f526,plain,
    ( ~ spl7_67
    | spl7_68
    | ~ spl7_12
    | spl7_37 ),
    inference(avatar_split_clause,[],[f508,f270,f144,f524,f518])).

fof(f518,plain,
    ( spl7_67
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f524,plain,
    ( spl7_68
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f270,plain,
    ( spl7_37
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f508,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl7_12
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f500,f271])).

fof(f271,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f270])).

fof(f500,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl7_12 ),
    inference(resolution,[],[f378,f145])).

fof(f378,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f171,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',t2_subset)).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f79,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',antisymmetry_r2_hidden)).

fof(f497,plain,
    ( ~ spl7_65
    | spl7_60
    | spl7_49 ),
    inference(avatar_split_clause,[],[f376,f349,f479,f495])).

fof(f495,plain,
    ( spl7_65
  <=> ~ m1_subset_1(k15_lattice3(sK0,sK2),sK3(sK1,k15_lattice3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f479,plain,
    ( spl7_60
  <=> v1_xboole_0(sK3(sK1,k15_lattice3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f349,plain,
    ( spl7_49
  <=> ~ r2_hidden(k15_lattice3(sK0,sK2),sK3(sK1,k15_lattice3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f376,plain,
    ( v1_xboole_0(sK3(sK1,k15_lattice3(sK0,sK2)))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),sK3(sK1,k15_lattice3(sK0,sK2)))
    | ~ spl7_49 ),
    inference(resolution,[],[f350,f79])).

fof(f350,plain,
    ( ~ r2_hidden(k15_lattice3(sK0,sK2),sK3(sK1,k15_lattice3(sK0,sK2)))
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f349])).

fof(f490,plain,
    ( ~ spl7_63
    | spl7_56
    | spl7_41 ),
    inference(avatar_split_clause,[],[f375,f311,f407,f488])).

fof(f488,plain,
    ( spl7_63
  <=> ~ m1_subset_1(k15_lattice3(sK0,sK2),sK3(k15_lattice3(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f407,plain,
    ( spl7_56
  <=> v1_xboole_0(sK3(k15_lattice3(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f311,plain,
    ( spl7_41
  <=> ~ r2_hidden(k15_lattice3(sK0,sK2),sK3(k15_lattice3(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f375,plain,
    ( v1_xboole_0(sK3(k15_lattice3(sK0,sK2),sK1))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),sK3(k15_lattice3(sK0,sK2),sK1))
    | ~ spl7_41 ),
    inference(resolution,[],[f312,f79])).

fof(f312,plain,
    ( ~ r2_hidden(k15_lattice3(sK0,sK2),sK3(k15_lattice3(sK0,sK2),sK1))
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f311])).

fof(f481,plain,
    ( ~ spl7_59
    | spl7_60
    | spl7_53 ),
    inference(avatar_split_clause,[],[f374,f368,f479,f473])).

fof(f473,plain,
    ( spl7_59
  <=> ~ m1_subset_1(sK1,sK3(sK1,k15_lattice3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f368,plain,
    ( spl7_53
  <=> ~ r2_hidden(sK1,sK3(sK1,k15_lattice3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f374,plain,
    ( v1_xboole_0(sK3(sK1,k15_lattice3(sK0,sK2)))
    | ~ m1_subset_1(sK1,sK3(sK1,k15_lattice3(sK0,sK2)))
    | ~ spl7_53 ),
    inference(resolution,[],[f369,f79])).

fof(f369,plain,
    ( ~ r2_hidden(sK1,sK3(sK1,k15_lattice3(sK0,sK2)))
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f368])).

fof(f409,plain,
    ( ~ spl7_55
    | spl7_56
    | spl7_45 ),
    inference(avatar_split_clause,[],[f337,f333,f407,f401])).

fof(f401,plain,
    ( spl7_55
  <=> ~ m1_subset_1(sK1,sK3(k15_lattice3(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f333,plain,
    ( spl7_45
  <=> ~ r2_hidden(sK1,sK3(k15_lattice3(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f337,plain,
    ( v1_xboole_0(sK3(k15_lattice3(sK0,sK2),sK1))
    | ~ m1_subset_1(sK1,sK3(k15_lattice3(sK0,sK2),sK1))
    | ~ spl7_45 ),
    inference(resolution,[],[f334,f79])).

fof(f334,plain,
    ( ~ r2_hidden(sK1,sK3(k15_lattice3(sK0,sK2),sK1))
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f333])).

fof(f373,plain,
    ( spl7_46
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f360,f226,f339])).

fof(f339,plain,
    ( spl7_46
  <=> m1_subset_1(sK3(sK1,k15_lattice3(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f226,plain,
    ( spl7_28
  <=> r2_hidden(sK3(sK1,k15_lattice3(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f360,plain,
    ( m1_subset_1(sK3(sK1,k15_lattice3(sK0,sK2)),sK1)
    | ~ spl7_28 ),
    inference(resolution,[],[f227,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',t1_subset)).

fof(f227,plain,
    ( r2_hidden(sK3(sK1,k15_lattice3(sK0,sK2)),sK1)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f226])).

fof(f370,plain,
    ( ~ spl7_53
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f359,f226,f368])).

fof(f359,plain,
    ( ~ r2_hidden(sK1,sK3(sK1,k15_lattice3(sK0,sK2)))
    | ~ spl7_28 ),
    inference(resolution,[],[f227,f81])).

fof(f363,plain,
    ( ~ spl7_28
    | spl7_47 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | ~ spl7_28
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f360,f343])).

fof(f343,plain,
    ( ~ m1_subset_1(sK3(sK1,k15_lattice3(sK0,sK2)),sK1)
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl7_47
  <=> ~ m1_subset_1(sK3(sK1,k15_lattice3(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f358,plain,
    ( spl7_50
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f255,f232,f356])).

fof(f356,plain,
    ( spl7_50
  <=> m1_subset_1(sK3(sK1,k15_lattice3(sK0,sK2)),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f232,plain,
    ( spl7_30
  <=> r2_hidden(sK3(sK1,k15_lattice3(sK0,sK2)),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f255,plain,
    ( m1_subset_1(sK3(sK1,k15_lattice3(sK0,sK2)),k15_lattice3(sK0,sK2))
    | ~ spl7_30 ),
    inference(resolution,[],[f233,f80])).

fof(f233,plain,
    ( r2_hidden(sK3(sK1,k15_lattice3(sK0,sK2)),k15_lattice3(sK0,sK2))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f232])).

fof(f351,plain,
    ( ~ spl7_49
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f254,f232,f349])).

fof(f254,plain,
    ( ~ r2_hidden(k15_lattice3(sK0,sK2),sK3(sK1,k15_lattice3(sK0,sK2)))
    | ~ spl7_30 ),
    inference(resolution,[],[f233,f81])).

fof(f344,plain,
    ( ~ spl7_47
    | spl7_36
    | spl7_29 ),
    inference(avatar_split_clause,[],[f239,f229,f273,f342])).

fof(f273,plain,
    ( spl7_36
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f229,plain,
    ( spl7_29
  <=> ~ r2_hidden(sK3(sK1,k15_lattice3(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f239,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3(sK1,k15_lattice3(sK0,sK2)),sK1)
    | ~ spl7_29 ),
    inference(resolution,[],[f230,f79])).

fof(f230,plain,
    ( ~ r2_hidden(sK3(sK1,k15_lattice3(sK0,sK2)),sK1)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f229])).

fof(f336,plain,
    ( spl7_38
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f323,f208,f301])).

fof(f301,plain,
    ( spl7_38
  <=> m1_subset_1(sK3(k15_lattice3(sK0,sK2),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f208,plain,
    ( spl7_26
  <=> r2_hidden(sK3(k15_lattice3(sK0,sK2),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f323,plain,
    ( m1_subset_1(sK3(k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl7_26 ),
    inference(resolution,[],[f209,f80])).

fof(f209,plain,
    ( r2_hidden(sK3(k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f208])).

fof(f335,plain,
    ( ~ spl7_45
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f322,f208,f333])).

fof(f322,plain,
    ( ~ r2_hidden(sK1,sK3(k15_lattice3(sK0,sK2),sK1))
    | ~ spl7_26 ),
    inference(resolution,[],[f209,f81])).

fof(f326,plain,
    ( ~ spl7_26
    | spl7_39 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl7_26
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f323,f305])).

fof(f305,plain,
    ( ~ m1_subset_1(sK3(k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl7_39
  <=> ~ m1_subset_1(sK3(k15_lattice3(sK0,sK2),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f320,plain,
    ( spl7_42
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f222,f202,f318])).

fof(f318,plain,
    ( spl7_42
  <=> m1_subset_1(sK3(k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f202,plain,
    ( spl7_24
  <=> r2_hidden(sK3(k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f222,plain,
    ( m1_subset_1(sK3(k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))
    | ~ spl7_24 ),
    inference(resolution,[],[f203,f80])).

fof(f203,plain,
    ( r2_hidden(sK3(k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f202])).

fof(f313,plain,
    ( ~ spl7_41
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f221,f202,f311])).

fof(f221,plain,
    ( ~ r2_hidden(k15_lattice3(sK0,sK2),sK3(k15_lattice3(sK0,sK2),sK1))
    | ~ spl7_24 ),
    inference(resolution,[],[f203,f81])).

fof(f306,plain,
    ( ~ spl7_39
    | spl7_36
    | spl7_27 ),
    inference(avatar_split_clause,[],[f215,f211,f273,f304])).

fof(f211,plain,
    ( spl7_27
  <=> ~ r2_hidden(sK3(k15_lattice3(sK0,sK2),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f215,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3(k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl7_27 ),
    inference(resolution,[],[f212,f79])).

fof(f212,plain,
    ( ~ r2_hidden(sK3(k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f211])).

fof(f275,plain,
    ( ~ spl7_35
    | spl7_36
    | spl7_23 ),
    inference(avatar_split_clause,[],[f224,f185,f273,f267])).

fof(f267,plain,
    ( spl7_35
  <=> ~ m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f185,plain,
    ( spl7_23
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f224,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2,sK1)
    | ~ spl7_23 ),
    inference(resolution,[],[f186,f79])).

fof(f186,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f185])).

fof(f252,plain,
    ( ~ spl7_33
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f223,f202,f250])).

fof(f250,plain,
    ( spl7_33
  <=> ~ v1_xboole_0(k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f223,plain,
    ( ~ v1_xboole_0(k15_lattice3(sK0,sK2))
    | ~ spl7_24 ),
    inference(resolution,[],[f203,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',t7_boole)).

fof(f244,plain,
    ( spl7_15
    | spl7_29
    | spl7_31 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl7_15
    | ~ spl7_29
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f242,f152])).

fof(f242,plain,
    ( k15_lattice3(sK0,sK2) = sK1
    | ~ spl7_29
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f240,f230])).

fof(f240,plain,
    ( r2_hidden(sK3(sK1,k15_lattice3(sK0,sK2)),sK1)
    | k15_lattice3(sK0,sK2) = sK1
    | ~ spl7_31 ),
    inference(resolution,[],[f236,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',t2_tarski)).

fof(f236,plain,
    ( ~ r2_hidden(sK3(sK1,k15_lattice3(sK0,sK2)),k15_lattice3(sK0,sK2))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl7_31
  <=> ~ r2_hidden(sK3(sK1,k15_lattice3(sK0,sK2)),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f237,plain,
    ( ~ spl7_29
    | ~ spl7_31
    | spl7_15 ),
    inference(avatar_split_clause,[],[f196,f151,f235,f229])).

fof(f196,plain,
    ( ~ r2_hidden(sK3(sK1,k15_lattice3(sK0,sK2)),k15_lattice3(sK0,sK2))
    | ~ r2_hidden(sK3(sK1,k15_lattice3(sK0,sK2)),sK1)
    | ~ spl7_15 ),
    inference(extensionality_resolution,[],[f68,f152])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f220,plain,
    ( spl7_15
    | spl7_25
    | spl7_27 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f218,f152])).

fof(f218,plain,
    ( k15_lattice3(sK0,sK2) = sK1
    | ~ spl7_25
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f216,f212])).

fof(f216,plain,
    ( r2_hidden(sK3(k15_lattice3(sK0,sK2),sK1),sK1)
    | k15_lattice3(sK0,sK2) = sK1
    | ~ spl7_25 ),
    inference(resolution,[],[f206,f67])).

fof(f206,plain,
    ( ~ r2_hidden(sK3(k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl7_25
  <=> ~ r2_hidden(sK3(k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f213,plain,
    ( ~ spl7_25
    | ~ spl7_27
    | spl7_15 ),
    inference(avatar_split_clause,[],[f195,f151,f211,f205])).

fof(f195,plain,
    ( ~ r2_hidden(sK3(k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ r2_hidden(sK3(k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))
    | ~ spl7_15 ),
    inference(extensionality_resolution,[],[f68,f152])).

fof(f187,plain,
    ( ~ spl7_23
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f163,f130,f185])).

fof(f163,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl7_8 ),
    inference(resolution,[],[f81,f131])).

fof(f180,plain,
    ( spl7_20
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f162,f130,f178])).

fof(f178,plain,
    ( spl7_20
  <=> m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f162,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f80,f131])).

fof(f170,plain,
    ( ~ spl7_19
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f161,f130,f168])).

fof(f168,plain,
    ( spl7_19
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f161,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f78,f131])).

fof(f160,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f87,f158])).

fof(f158,plain,
    ( spl7_16
  <=> l3_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f87,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',existence_l3_lattices)).

fof(f153,plain,(
    ~ spl7_15 ),
    inference(avatar_split_clause,[],[f60,f151])).

fof(f60,plain,(
    k15_lattice3(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k15_lattice3(X0,X2) != X1
              & r4_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k15_lattice3(X0,X2) != X1
              & r4_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
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
                ( ( r4_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k15_lattice3(X0,X2) = X1 ) ) ) ),
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
              ( ( r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k15_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',t41_lattice3)).

fof(f146,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f61,f144])).

fof(f61,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f139,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f59,f137])).

fof(f59,plain,(
    r4_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f132,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f58,f130])).

fof(f58,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f125,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f65,f123])).

fof(f65,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f118,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f64,f116])).

fof(f64,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f111,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f63,f109])).

fof(f63,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f62,f102])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
