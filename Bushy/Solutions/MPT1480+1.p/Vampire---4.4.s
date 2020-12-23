%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattice3__t13_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:53 EDT 2019

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 378 expanded)
%              Number of leaves         :   22 ( 172 expanded)
%              Depth                    :   15
%              Number of atoms          :  942 (1716 expanded)
%              Number of equality atoms :   53 ( 108 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20996,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f90,f94,f98,f102,f119,f135,f348,f352,f412,f1635,f20007,f20100,f20104,f20160,f20164,f20256,f20434,f20995])).

fof(f20995,plain,
    ( spl9_30
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | spl9_15
    | ~ spl9_18
    | ~ spl9_32
    | ~ spl9_34
    | ~ spl9_836 ),
    inference(avatar_split_clause,[],[f20956,f20432,f410,f346,f133,f117,f100,f96,f92,f88,f84,f286])).

fof(f286,plain,
    ( spl9_30
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f84,plain,
    ( spl9_0
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f88,plain,
    ( spl9_2
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f92,plain,
    ( spl9_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f96,plain,
    ( spl9_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f100,plain,
    ( spl9_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f117,plain,
    ( spl9_15
  <=> k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f133,plain,
    ( spl9_18
  <=> m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f346,plain,
    ( spl9_32
  <=> r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f410,plain,
    ( spl9_34
  <=> r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f20432,plain,
    ( spl9_836
  <=> r1_orders_2(sK0,k10_lattice3(sK0,sK2,sK1),sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_836])])).

fof(f20956,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_15
    | ~ spl9_18
    | ~ spl9_32
    | ~ spl9_34
    | ~ spl9_836 ),
    inference(subsumption_resolution,[],[f20955,f118])).

fof(f118,plain,
    ( k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK2,sK1)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f20955,plain,
    ( v2_struct_0(sK0)
    | k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_32
    | ~ spl9_34
    | ~ spl9_836 ),
    inference(subsumption_resolution,[],[f20954,f347])).

fof(f347,plain,
    ( r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f346])).

fof(f20954,plain,
    ( ~ r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | v2_struct_0(sK0)
    | k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_34
    | ~ spl9_836 ),
    inference(subsumption_resolution,[],[f20953,f411])).

fof(f411,plain,
    ( r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1))
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f410])).

fof(f20953,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1))
    | ~ r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | v2_struct_0(sK0)
    | k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_836 ),
    inference(subsumption_resolution,[],[f20952,f134])).

fof(f134,plain,
    ( m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f133])).

fof(f20952,plain,
    ( ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1))
    | ~ r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | v2_struct_0(sK0)
    | k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_836 ),
    inference(subsumption_resolution,[],[f20951,f97])).

fof(f97,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f20951,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1))
    | ~ r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | v2_struct_0(sK0)
    | k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_836 ),
    inference(subsumption_resolution,[],[f20950,f101])).

fof(f101,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f20950,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1))
    | ~ r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | v2_struct_0(sK0)
    | k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_836 ),
    inference(subsumption_resolution,[],[f20949,f93])).

fof(f93,plain,
    ( l1_orders_2(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f20949,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1))
    | ~ r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | v2_struct_0(sK0)
    | k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_836 ),
    inference(subsumption_resolution,[],[f20948,f89])).

fof(f89,plain,
    ( v1_lattice3(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f20948,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1))
    | ~ r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | v2_struct_0(sK0)
    | k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)
    | ~ spl9_0
    | ~ spl9_836 ),
    inference(subsumption_resolution,[],[f20930,f85])).

fof(f85,plain,
    ( v5_orders_2(sK0)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f84])).

fof(f20930,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1))
    | ~ r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | v2_struct_0(sK0)
    | k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)
    | ~ spl9_836 ),
    inference(resolution,[],[f20433,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | v2_struct_0(X0)
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t13_lattice3.p',l26_lattice3)).

fof(f20433,plain,
    ( r1_orders_2(sK0,k10_lattice3(sK0,sK2,sK1),sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)))
    | ~ spl9_836 ),
    inference(avatar_component_clause,[],[f20432])).

fof(f20434,plain,
    ( spl9_836
    | ~ spl9_98
    | ~ spl9_812
    | ~ spl9_816
    | ~ spl9_820 ),
    inference(avatar_split_clause,[],[f20282,f20254,f20158,f20098,f1633,f20432])).

fof(f1633,plain,
    ( spl9_98
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k10_lattice3(sK0,sK2,sK1),X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_98])])).

fof(f20098,plain,
    ( spl9_812
  <=> m1_subset_1(sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_812])])).

fof(f20158,plain,
    ( spl9_816
  <=> r1_orders_2(sK0,sK1,sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_816])])).

fof(f20254,plain,
    ( spl9_820
  <=> r1_orders_2(sK0,sK2,sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_820])])).

fof(f20282,plain,
    ( r1_orders_2(sK0,k10_lattice3(sK0,sK2,sK1),sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)))
    | ~ spl9_98
    | ~ spl9_812
    | ~ spl9_816
    | ~ spl9_820 ),
    inference(subsumption_resolution,[],[f20281,f20099])).

fof(f20099,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0))
    | ~ spl9_812 ),
    inference(avatar_component_clause,[],[f20098])).

fof(f20281,plain,
    ( r1_orders_2(sK0,k10_lattice3(sK0,sK2,sK1),sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)))
    | ~ m1_subset_1(sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0))
    | ~ spl9_98
    | ~ spl9_816
    | ~ spl9_820 ),
    inference(subsumption_resolution,[],[f20263,f20159])).

fof(f20159,plain,
    ( r1_orders_2(sK0,sK1,sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)))
    | ~ spl9_816 ),
    inference(avatar_component_clause,[],[f20158])).

fof(f20263,plain,
    ( r1_orders_2(sK0,k10_lattice3(sK0,sK2,sK1),sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)))
    | ~ r1_orders_2(sK0,sK1,sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)))
    | ~ m1_subset_1(sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0))
    | ~ spl9_98
    | ~ spl9_820 ),
    inference(resolution,[],[f20255,f1634])).

fof(f1634,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,k10_lattice3(sK0,sK2,sK1),X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_98 ),
    inference(avatar_component_clause,[],[f1633])).

fof(f20255,plain,
    ( r1_orders_2(sK0,sK2,sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)))
    | ~ spl9_820 ),
    inference(avatar_component_clause,[],[f20254])).

fof(f20256,plain,
    ( spl9_820
    | ~ spl9_6
    | spl9_15
    | ~ spl9_32
    | ~ spl9_818 ),
    inference(avatar_split_clause,[],[f20252,f20162,f346,f117,f96,f20254])).

fof(f20162,plain,
    ( spl9_818
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X2)
        | r1_orders_2(sK0,X2,sK3(sK0,sK1,X2,k10_lattice3(sK0,sK2,sK1)))
        | ~ r1_orders_2(sK0,X2,k10_lattice3(sK0,sK2,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_818])])).

fof(f20252,plain,
    ( r1_orders_2(sK0,sK2,sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)))
    | ~ spl9_6
    | ~ spl9_15
    | ~ spl9_32
    | ~ spl9_818 ),
    inference(subsumption_resolution,[],[f20251,f97])).

fof(f20251,plain,
    ( r1_orders_2(sK0,sK2,sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_15
    | ~ spl9_32
    | ~ spl9_818 ),
    inference(subsumption_resolution,[],[f20238,f118])).

fof(f20238,plain,
    ( k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK2,sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_32
    | ~ spl9_818 ),
    inference(resolution,[],[f20163,f347])).

fof(f20163,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK0,X2,k10_lattice3(sK0,sK2,sK1))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X2)
        | r1_orders_2(sK0,X2,sK3(sK0,sK1,X2,k10_lattice3(sK0,sK2,sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl9_818 ),
    inference(avatar_component_clause,[],[f20162])).

fof(f20164,plain,
    ( spl9_30
    | spl9_818
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f440,f410,f133,f100,f92,f88,f84,f20162,f286])).

fof(f440,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X2,k10_lattice3(sK0,sK2,sK1))
        | r1_orders_2(sK0,X2,sK3(sK0,sK1,X2,k10_lattice3(sK0,sK2,sK1)))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X2) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f439,f134])).

fof(f439,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X2,k10_lattice3(sK0,sK2,sK1))
        | r1_orders_2(sK0,X2,sK3(sK0,sK1,X2,k10_lattice3(sK0,sK2,sK1)))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X2) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f438,f101])).

fof(f438,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X2,k10_lattice3(sK0,sK2,sK1))
        | r1_orders_2(sK0,X2,sK3(sK0,sK1,X2,k10_lattice3(sK0,sK2,sK1)))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X2) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f437,f93])).

fof(f437,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X2,k10_lattice3(sK0,sK2,sK1))
        | r1_orders_2(sK0,X2,sK3(sK0,sK1,X2,k10_lattice3(sK0,sK2,sK1)))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X2) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f436,f89])).

fof(f436,plain,
    ( ! [X2] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X2,k10_lattice3(sK0,sK2,sK1))
        | r1_orders_2(sK0,X2,sK3(sK0,sK1,X2,k10_lattice3(sK0,sK2,sK1)))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X2) )
    | ~ spl9_0
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f415,f85])).

fof(f415,plain,
    ( ! [X2] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X2,k10_lattice3(sK0,sK2,sK1))
        | r1_orders_2(sK0,X2,sK3(sK0,sK1,X2,k10_lattice3(sK0,sK2,sK1)))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X2) )
    | ~ spl9_34 ),
    inference(resolution,[],[f411,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X3)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f20160,plain,
    ( spl9_816
    | ~ spl9_6
    | spl9_15
    | ~ spl9_32
    | ~ spl9_814 ),
    inference(avatar_split_clause,[],[f20156,f20102,f346,f117,f96,f20158])).

fof(f20102,plain,
    ( spl9_814
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X1)
        | r1_orders_2(sK0,sK1,sK3(sK0,sK1,X1,k10_lattice3(sK0,sK2,sK1)))
        | ~ r1_orders_2(sK0,X1,k10_lattice3(sK0,sK2,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_814])])).

fof(f20156,plain,
    ( r1_orders_2(sK0,sK1,sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)))
    | ~ spl9_6
    | ~ spl9_15
    | ~ spl9_32
    | ~ spl9_814 ),
    inference(subsumption_resolution,[],[f20155,f97])).

fof(f20155,plain,
    ( r1_orders_2(sK0,sK1,sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_15
    | ~ spl9_32
    | ~ spl9_814 ),
    inference(subsumption_resolution,[],[f20141,f118])).

fof(f20141,plain,
    ( k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_32
    | ~ spl9_814 ),
    inference(resolution,[],[f20103,f347])).

fof(f20103,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,X1,k10_lattice3(sK0,sK2,sK1))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X1)
        | r1_orders_2(sK0,sK1,sK3(sK0,sK1,X1,k10_lattice3(sK0,sK2,sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_814 ),
    inference(avatar_component_clause,[],[f20102])).

fof(f20104,plain,
    ( spl9_30
    | spl9_814
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f435,f410,f133,f100,f92,f88,f84,f20102,f286])).

fof(f435,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X1,k10_lattice3(sK0,sK2,sK1))
        | r1_orders_2(sK0,sK1,sK3(sK0,sK1,X1,k10_lattice3(sK0,sK2,sK1)))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X1) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f434,f134])).

fof(f434,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X1,k10_lattice3(sK0,sK2,sK1))
        | r1_orders_2(sK0,sK1,sK3(sK0,sK1,X1,k10_lattice3(sK0,sK2,sK1)))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X1) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f433,f101])).

fof(f433,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X1,k10_lattice3(sK0,sK2,sK1))
        | r1_orders_2(sK0,sK1,sK3(sK0,sK1,X1,k10_lattice3(sK0,sK2,sK1)))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X1) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f432,f93])).

fof(f432,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X1,k10_lattice3(sK0,sK2,sK1))
        | r1_orders_2(sK0,sK1,sK3(sK0,sK1,X1,k10_lattice3(sK0,sK2,sK1)))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X1) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f431,f89])).

fof(f431,plain,
    ( ! [X1] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X1,k10_lattice3(sK0,sK2,sK1))
        | r1_orders_2(sK0,sK1,sK3(sK0,sK1,X1,k10_lattice3(sK0,sK2,sK1)))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X1) )
    | ~ spl9_0
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f414,f85])).

fof(f414,plain,
    ( ! [X1] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X1,k10_lattice3(sK0,sK2,sK1))
        | r1_orders_2(sK0,sK1,sK3(sK0,sK1,X1,k10_lattice3(sK0,sK2,sK1)))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X1) )
    | ~ spl9_34 ),
    inference(resolution,[],[f411,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X3)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f20100,plain,
    ( spl9_812
    | ~ spl9_6
    | spl9_15
    | ~ spl9_32
    | ~ spl9_810 ),
    inference(avatar_split_clause,[],[f20096,f20005,f346,f117,f96,f20098])).

fof(f20005,plain,
    ( spl9_810
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X0)
        | m1_subset_1(sK3(sK0,sK1,X0,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,k10_lattice3(sK0,sK2,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_810])])).

fof(f20096,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0))
    | ~ spl9_6
    | ~ spl9_15
    | ~ spl9_32
    | ~ spl9_810 ),
    inference(subsumption_resolution,[],[f20095,f97])).

fof(f20095,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_15
    | ~ spl9_32
    | ~ spl9_810 ),
    inference(subsumption_resolution,[],[f20081,f118])).

fof(f20081,plain,
    ( k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK2,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_32
    | ~ spl9_810 ),
    inference(resolution,[],[f20006,f347])).

fof(f20006,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,k10_lattice3(sK0,sK2,sK1))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X0)
        | m1_subset_1(sK3(sK0,sK1,X0,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_810 ),
    inference(avatar_component_clause,[],[f20005])).

fof(f20007,plain,
    ( spl9_30
    | spl9_810
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f430,f410,f133,f100,f92,f88,f84,f20005,f286])).

fof(f430,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X0,k10_lattice3(sK0,sK2,sK1))
        | m1_subset_1(sK3(sK0,sK1,X0,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X0) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f429,f134])).

fof(f429,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X0,k10_lattice3(sK0,sK2,sK1))
        | m1_subset_1(sK3(sK0,sK1,X0,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X0) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f428,f101])).

fof(f428,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X0,k10_lattice3(sK0,sK2,sK1))
        | m1_subset_1(sK3(sK0,sK1,X0,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X0) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f427,f93])).

fof(f427,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X0,k10_lattice3(sK0,sK2,sK1))
        | m1_subset_1(sK3(sK0,sK1,X0,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X0) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f426,f89])).

fof(f426,plain,
    ( ! [X0] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X0,k10_lattice3(sK0,sK2,sK1))
        | m1_subset_1(sK3(sK0,sK1,X0,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X0) )
    | ~ spl9_0
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f413,f85])).

fof(f413,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r1_orders_2(sK0,X0,k10_lattice3(sK0,sK2,sK1))
        | m1_subset_1(sK3(sK0,sK1,X0,k10_lattice3(sK0,sK2,sK1)),u1_struct_0(sK0))
        | k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,X0) )
    | ~ spl9_34 ),
    inference(resolution,[],[f411,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X3)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1635,plain,
    ( spl9_98
    | spl9_30
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f174,f133,f100,f96,f92,f88,f84,f286,f1633])).

fof(f174,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | r1_orders_2(sK0,k10_lattice3(sK0,sK2,sK1),X0) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f173,f101])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | r1_orders_2(sK0,k10_lattice3(sK0,sK2,sK1),X0) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f172,f97])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | r1_orders_2(sK0,k10_lattice3(sK0,sK2,sK1),X0) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f171,f93])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | r1_orders_2(sK0,k10_lattice3(sK0,sK2,sK1),X0) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f170,f89])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | r1_orders_2(sK0,k10_lattice3(sK0,sK2,sK1),X0) )
    | ~ spl9_0
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f163,f85])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | r1_orders_2(sK0,k10_lattice3(sK0,sK2,sK1),X0) )
    | ~ spl9_18 ),
    inference(resolution,[],[f134,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X4)
      | ~ r1_orders_2(X0,X2,X4)
      | r1_orders_2(X0,k10_lattice3(X0,X1,X2),X4) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X4)
      | ~ r1_orders_2(X0,X2,X4)
      | r1_orders_2(X0,X3,X4)
      | k10_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f412,plain,
    ( spl9_34
    | spl9_30
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f184,f133,f100,f96,f92,f88,f84,f286,f410])).

fof(f184,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f183,f101])).

fof(f183,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f182,f97])).

fof(f182,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f181,f93])).

fof(f181,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f180,f89])).

fof(f180,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1))
    | ~ spl9_0
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f165,f85])).

fof(f165,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK2,sK1))
    | ~ spl9_18 ),
    inference(resolution,[],[f134,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f352,plain,
    ( ~ spl9_2
    | ~ spl9_4
    | ~ spl9_30 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f350,f93])).

fof(f350,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl9_2
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f349,f89])).

fof(f349,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl9_30 ),
    inference(resolution,[],[f287,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t13_lattice3.p',cc1_lattice3)).

fof(f287,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f286])).

fof(f348,plain,
    ( spl9_32
    | spl9_30
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f179,f133,f100,f96,f92,f88,f84,f286,f346])).

fof(f179,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f178,f101])).

fof(f178,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f177,f97])).

fof(f177,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f176,f93])).

fof(f176,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f175,f89])).

fof(f175,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | ~ spl9_0
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f164,f85])).

fof(f164,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK2,sK1))
    | ~ spl9_18 ),
    inference(resolution,[],[f134,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f135,plain,
    ( spl9_18
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f124,f100,f96,f92,f133])).

fof(f124,plain,
    ( m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(resolution,[],[f105,f101])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k10_lattice3(sK0,sK2,X0),u1_struct_0(sK0)) )
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f103,f93])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k10_lattice3(sK0,sK2,X0),u1_struct_0(sK0)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f97,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t13_lattice3.p',dt_k10_lattice3)).

fof(f119,plain,(
    ~ spl9_15 ),
    inference(avatar_split_clause,[],[f40,f117])).

fof(f40,plain,(
    k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t13_lattice3.p',t13_lattice3)).

fof(f102,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f41,f100])).

fof(f41,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f39,f96])).

fof(f39,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f94,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f44,f92])).

fof(f44,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f43,f88])).

fof(f43,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f42,f84])).

fof(f42,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
