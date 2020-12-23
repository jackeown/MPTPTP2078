%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1217+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:30 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  235 ( 503 expanded)
%              Number of leaves         :   53 ( 233 expanded)
%              Depth                    :    9
%              Number of atoms          : 1027 (2434 expanded)
%              Number of equality atoms :   51 (  77 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2074,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f111,f126,f128,f156,f158,f189,f191,f200,f202,f204,f223,f262,f264,f269,f272,f287,f289,f332,f366,f368,f374,f376,f388,f390,f401,f656,f689,f1783,f1890,f1911,f1938,f2007,f2073])).

fof(f2073,plain,
    ( spl4_2
    | ~ spl4_8
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_40
    | spl4_42
    | ~ spl4_177 ),
    inference(avatar_split_clause,[],[f2060,f1883,f398,f381,f175,f135,f147,f102])).

fof(f102,plain,
    ( spl4_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f147,plain,
    ( spl4_8
  <=> v6_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f135,plain,
    ( spl4_5
  <=> l1_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f175,plain,
    ( spl4_12
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f381,plain,
    ( spl4_40
  <=> m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f398,plain,
    ( spl4_42
  <=> k5_lattices(sK1) = k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f1883,plain,
    ( spl4_177
  <=> k5_lattices(sK1) = k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_177])])).

fof(f2060,plain,
    ( k5_lattices(sK1) = k4_lattices(sK1,sK2,k7_lattices(sK1,sK3))
    | ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_lattices(sK1)
    | ~ v6_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_177 ),
    inference(superposition,[],[f94,f1885])).

fof(f1885,plain,
    ( k5_lattices(sK1) = k2_lattices(sK1,sK2,k7_lattices(sK1,sK3))
    | ~ spl4_177 ),
    inference(avatar_component_clause,[],[f1883])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f2007,plain,
    ( spl4_2
    | ~ spl4_10
    | ~ spl4_35
    | ~ spl4_1
    | ~ spl4_175
    | spl4_178 ),
    inference(avatar_split_clause,[],[f2005,f1887,f1875,f98,f351,f167,f102])).

fof(f167,plain,
    ( spl4_10
  <=> v10_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f351,plain,
    ( spl4_35
  <=> v13_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f98,plain,
    ( spl4_1
  <=> l3_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1875,plain,
    ( spl4_175
  <=> m1_subset_1(k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_175])])).

fof(f1887,plain,
    ( spl4_178
  <=> r3_lattices(sK1,k5_lattices(sK1),k2_lattices(sK1,sK2,k7_lattices(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_178])])).

fof(f2005,plain,
    ( ~ m1_subset_1(k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)),u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v13_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | spl4_178 ),
    inference(resolution,[],[f1889,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r3_lattices(X0,k5_lattices(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattices)).

fof(f1889,plain,
    ( ~ r3_lattices(sK1,k5_lattices(sK1),k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)))
    | spl4_178 ),
    inference(avatar_component_clause,[],[f1887])).

fof(f1938,plain,
    ( spl4_2
    | ~ spl4_8
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_40
    | spl4_182 ),
    inference(avatar_split_clause,[],[f1937,f1908,f381,f175,f135,f147,f102])).

fof(f1908,plain,
    ( spl4_182
  <=> m1_subset_1(k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_182])])).

fof(f1937,plain,
    ( ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_lattices(sK1)
    | ~ v6_lattices(sK1)
    | v2_struct_0(sK1)
    | spl4_182 ),
    inference(resolution,[],[f1910,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f1910,plain,
    ( ~ m1_subset_1(k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)),u1_struct_0(sK1))
    | spl4_182 ),
    inference(avatar_component_clause,[],[f1908])).

fof(f1911,plain,
    ( spl4_2
    | ~ spl4_8
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_40
    | ~ spl4_182
    | spl4_175 ),
    inference(avatar_split_clause,[],[f1906,f1875,f1908,f381,f175,f135,f147,f102])).

fof(f1906,plain,
    ( ~ m1_subset_1(k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_lattices(sK1)
    | ~ v6_lattices(sK1)
    | v2_struct_0(sK1)
    | spl4_175 ),
    inference(superposition,[],[f1877,f94])).

fof(f1877,plain,
    ( ~ m1_subset_1(k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)),u1_struct_0(sK1))
    | spl4_175 ),
    inference(avatar_component_clause,[],[f1875])).

fof(f1890,plain,
    ( ~ spl4_31
    | ~ spl4_175
    | spl4_177
    | ~ spl4_178
    | ~ spl4_24
    | ~ spl4_165 ),
    inference(avatar_split_clause,[],[f1870,f1780,f260,f1887,f1883,f1875,f322])).

fof(f322,plain,
    ( spl4_31
  <=> m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f260,plain,
    ( spl4_24
  <=> ! [X3,X2] :
        ( ~ r3_lattices(sK1,X2,X3)
        | ~ r1_lattices(sK1,X3,X2)
        | X2 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f1780,plain,
    ( spl4_165
  <=> r1_lattices(sK1,k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)),k5_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_165])])).

fof(f1870,plain,
    ( ~ r3_lattices(sK1,k5_lattices(sK1),k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)))
    | k5_lattices(sK1) = k2_lattices(sK1,sK2,k7_lattices(sK1,sK3))
    | ~ m1_subset_1(k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | ~ spl4_24
    | ~ spl4_165 ),
    inference(resolution,[],[f1782,f261])).

fof(f261,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattices(sK1,X3,X2)
        | ~ r3_lattices(sK1,X2,X3)
        | X2 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f260])).

fof(f1782,plain,
    ( r1_lattices(sK1,k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)),k5_lattices(sK1))
    | ~ spl4_165 ),
    inference(avatar_component_clause,[],[f1780])).

fof(f1783,plain,
    ( ~ spl4_40
    | spl4_165
    | ~ spl4_27
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f1757,f687,f283,f1780,f381])).

fof(f283,plain,
    ( spl4_27
  <=> k5_lattices(sK1) = k4_lattices(sK1,sK3,k7_lattices(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f687,plain,
    ( spl4_72
  <=> ! [X0] :
        ( r1_lattices(sK1,k2_lattices(sK1,sK2,X0),k4_lattices(sK1,sK3,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f1757,plain,
    ( r1_lattices(sK1,k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)),k5_lattices(sK1))
    | ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | ~ spl4_27
    | ~ spl4_72 ),
    inference(superposition,[],[f688,f285])).

fof(f285,plain,
    ( k5_lattices(sK1) = k4_lattices(sK1,sK3,k7_lattices(sK1,sK3))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f283])).

fof(f688,plain,
    ( ! [X0] :
        ( r1_lattices(sK1,k2_lattices(sK1,sK2,X0),k4_lattices(sK1,sK3,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f687])).

fof(f689,plain,
    ( spl4_2
    | ~ spl4_8
    | ~ spl4_5
    | ~ spl4_26
    | spl4_72
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f668,f654,f687,f279,f135,f147,f102])).

fof(f279,plain,
    ( spl4_26
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f654,plain,
    ( spl4_66
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_lattices(sK1,k2_lattices(sK1,sK2,X0),k2_lattices(sK1,sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f668,plain,
    ( ! [X0] :
        ( r1_lattices(sK1,k2_lattices(sK1,sK2,X0),k4_lattices(sK1,sK3,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3,u1_struct_0(sK1))
        | ~ l1_lattices(sK1)
        | ~ v6_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_66 ),
    inference(duplicate_literal_removal,[],[f667])).

fof(f667,plain,
    ( ! [X0] :
        ( r1_lattices(sK1,k2_lattices(sK1,sK2,X0),k4_lattices(sK1,sK3,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3,u1_struct_0(sK1))
        | ~ l1_lattices(sK1)
        | ~ v6_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_66 ),
    inference(superposition,[],[f655,f94])).

fof(f655,plain,
    ( ! [X0] :
        ( r1_lattices(sK1,k2_lattices(sK1,sK2,X0),k2_lattices(sK1,sK3,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f654])).

fof(f656,plain,
    ( spl4_66
    | ~ spl4_26
    | ~ spl4_12
    | ~ spl4_16
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f648,f364,f198,f175,f279,f654])).

fof(f198,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ r3_lattices(sK1,X0,X1)
        | r1_lattices(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f364,plain,
    ( spl4_38
  <=> ! [X1,X0,X2] :
        ( ~ r1_lattices(sK1,X0,X1)
        | r1_lattices(sK1,k2_lattices(sK1,X0,X2),k2_lattices(sK1,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f648,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_lattices(sK1,k2_lattices(sK1,sK2,X0),k2_lattices(sK1,sK3,X0)) )
    | ~ spl4_16
    | ~ spl4_38 ),
    inference(resolution,[],[f493,f64])).

fof(f64,plain,(
    r3_lattices(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ~ r3_lattices(sK1,k7_lattices(sK1,sK3),k7_lattices(sK1,sK2))
    & r3_lattices(sK1,sK2,sK3)
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v17_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f53,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
                & r3_lattices(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(sK1,k7_lattices(sK1,X2),k7_lattices(sK1,X1))
              & r3_lattices(sK1,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v17_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r3_lattices(sK1,k7_lattices(sK1,X2),k7_lattices(sK1,X1))
            & r3_lattices(sK1,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        & m1_subset_1(X1,u1_struct_0(sK1)) )
   => ( ? [X2] :
          ( ~ r3_lattices(sK1,k7_lattices(sK1,X2),k7_lattices(sK1,sK2))
          & r3_lattices(sK1,sK2,X2)
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X2] :
        ( ~ r3_lattices(sK1,k7_lattices(sK1,X2),k7_lattices(sK1,sK2))
        & r3_lattices(sK1,sK2,X2)
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ~ r3_lattices(sK1,k7_lattices(sK1,sK3),k7_lattices(sK1,sK2))
      & r3_lattices(sK1,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_lattices(X0,X1,X2)
                 => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
               => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).

fof(f493,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_lattices(sK1,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattices(sK1,k2_lattices(sK1,X0,X1),k2_lattices(sK1,X2,X1)) )
    | ~ spl4_16
    | ~ spl4_38 ),
    inference(duplicate_literal_removal,[],[f492])).

fof(f492,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattices(sK1,k2_lattices(sK1,X0,X1),k2_lattices(sK1,X2,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r3_lattices(sK1,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl4_16
    | ~ spl4_38 ),
    inference(resolution,[],[f365,f199])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK1,X0,X1)
        | ~ r3_lattices(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f198])).

fof(f365,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattices(sK1,X0,X1)
        | r1_lattices(sK1,k2_lattices(sK1,X0,X2),k2_lattices(sK1,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f364])).

fof(f401,plain,
    ( ~ spl4_40
    | ~ spl4_42
    | ~ spl4_4
    | spl4_41 ),
    inference(avatar_split_clause,[],[f396,f385,f124,f398,f381])).

fof(f124,plain,
    ( spl4_4
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k4_lattices(sK1,X0,X1) = k4_lattices(sK1,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f385,plain,
    ( spl4_41
  <=> k5_lattices(sK1) = k4_lattices(sK1,k7_lattices(sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f396,plain,
    ( k5_lattices(sK1) != k4_lattices(sK1,sK2,k7_lattices(sK1,sK3))
    | ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | ~ spl4_4
    | spl4_41 ),
    inference(superposition,[],[f387,f129])).

fof(f129,plain,
    ( ! [X0] :
        ( k4_lattices(sK1,sK2,X0) = k4_lattices(sK1,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f125,f62])).

fof(f62,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k4_lattices(sK1,X0,X1) = k4_lattices(sK1,X1,X0) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f387,plain,
    ( k5_lattices(sK1) != k4_lattices(sK1,k7_lattices(sK1,sK3),sK2)
    | spl4_41 ),
    inference(avatar_component_clause,[],[f385])).

fof(f390,plain,
    ( spl4_2
    | ~ spl4_1
    | ~ spl4_26
    | spl4_40 ),
    inference(avatar_split_clause,[],[f389,f381,f279,f98,f102])).

fof(f389,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | spl4_40 ),
    inference(resolution,[],[f383,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f383,plain,
    ( ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | spl4_40 ),
    inference(avatar_component_clause,[],[f381])).

fof(f388,plain,
    ( ~ spl4_12
    | ~ spl4_40
    | ~ spl4_41
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f377,f267,f385,f381,f175])).

fof(f267,plain,
    ( spl4_25
  <=> ! [X1,X0] :
        ( k4_lattices(sK1,X0,X1) != k5_lattices(sK1)
        | r3_lattices(sK1,X0,k7_lattices(sK1,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f377,plain,
    ( k5_lattices(sK1) != k4_lattices(sK1,k7_lattices(sK1,sK3),sK2)
    | ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl4_25 ),
    inference(resolution,[],[f268,f65])).

fof(f65,plain,(
    ~ r3_lattices(sK1,k7_lattices(sK1,sK3),k7_lattices(sK1,sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f268,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK1,X0,k7_lattices(sK1,X1))
        | k4_lattices(sK1,X0,X1) != k5_lattices(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f267])).

fof(f376,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_11
    | spl4_39 ),
    inference(avatar_split_clause,[],[f375,f371,f171,f102,f98])).

fof(f171,plain,
    ( spl4_11
  <=> v17_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f371,plain,
    ( spl4_39
  <=> v15_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f375,plain,
    ( ~ v17_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | spl4_39 ),
    inference(resolution,[],[f373,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).

fof(f373,plain,
    ( ~ v15_lattices(sK1)
    | spl4_39 ),
    inference(avatar_component_clause,[],[f371])).

fof(f374,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_39
    | spl4_35 ),
    inference(avatar_split_clause,[],[f369,f351,f371,f102,f98])).

fof(f369,plain,
    ( ~ v15_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | spl4_35 ),
    inference(resolution,[],[f353,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_lattices)).

fof(f353,plain,
    ( ~ v13_lattices(sK1)
    | spl4_35 ),
    inference(avatar_component_clause,[],[f351])).

fof(f368,plain,
    ( ~ spl4_3
    | spl4_37 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl4_3
    | spl4_37 ),
    inference(resolution,[],[f362,f116])).

fof(f116,plain,
    ( v7_lattices(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f108,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v7_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f108,plain,
    ( sP0(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_3
  <=> sP0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f362,plain,
    ( ~ v7_lattices(sK1)
    | spl4_37 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl4_37
  <=> v7_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f366,plain,
    ( spl4_2
    | ~ spl4_37
    | ~ spl4_15
    | ~ spl4_1
    | spl4_38
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f358,f106,f364,f98,f194,f360,f102])).

fof(f194,plain,
    ( spl4_15
  <=> v8_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f358,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattices(sK1,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l3_lattices(sK1)
        | r1_lattices(sK1,k2_lattices(sK1,X0,X2),k2_lattices(sK1,X1,X2))
        | ~ v8_lattices(sK1)
        | ~ v7_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f84,f118])).

fof(f118,plain,
    ( v9_lattices(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f108,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattices(X0,X1,X2)
                   => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_lattices)).

fof(f332,plain,
    ( spl4_2
    | ~ spl4_5
    | spl4_31 ),
    inference(avatar_split_clause,[],[f331,f322,f135,f102])).

fof(f331,plain,
    ( ~ l1_lattices(sK1)
    | v2_struct_0(sK1)
    | spl4_31 ),
    inference(resolution,[],[f324,f89])).

fof(f89,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f324,plain,
    ( ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | spl4_31 ),
    inference(avatar_component_clause,[],[f322])).

fof(f289,plain,(
    spl4_26 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl4_26 ),
    inference(resolution,[],[f281,f63])).

fof(f63,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f281,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f279])).

fof(f287,plain,
    ( spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_1
    | ~ spl4_26
    | spl4_27
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f276,f221,f283,f279,f98,f171,f167,f102])).

fof(f221,plain,
    ( spl4_18
  <=> ! [X0] :
        ( k4_lattices(sK1,sK3,k7_lattices(sK1,X0)) = k4_lattices(sK1,k7_lattices(sK1,X0),sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f276,plain,
    ( k5_lattices(sK1) = k4_lattices(sK1,sK3,k7_lattices(sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_18 ),
    inference(duplicate_literal_removal,[],[f274])).

fof(f274,plain,
    ( k5_lattices(sK1) = k4_lattices(sK1,sK3,k7_lattices(sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl4_18 ),
    inference(superposition,[],[f86,f222])).

fof(f222,plain,
    ( ! [X0] :
        ( k4_lattices(sK1,sK3,k7_lattices(sK1,X0)) = k4_lattices(sK1,k7_lattices(sK1,X0),sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f221])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattices)).

fof(f272,plain,(
    spl4_23 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl4_23 ),
    inference(resolution,[],[f270,f61])).

fof(f61,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f270,plain,
    ( ~ l3_lattices(sK1)
    | spl4_23 ),
    inference(resolution,[],[f258,f67])).

fof(f67,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f258,plain,
    ( ~ l2_lattices(sK1)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl4_23
  <=> l2_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f269,plain,
    ( spl4_2
    | ~ spl4_10
    | ~ spl4_1
    | spl4_25 ),
    inference(avatar_split_clause,[],[f265,f267,f98,f167,f102])).

fof(f265,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK1,X0,X1) != k5_lattices(sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | r3_lattices(sK1,X0,k7_lattices(sK1,X1))
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f87,f60])).

fof(f60,plain,(
    v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | k4_lattices(X0,X1,X2) != k5_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,k7_lattices(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
                  | ~ r3_lattices(X0,X1,k7_lattices(X0,X2)) )
                & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) != k5_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_lattices)).

fof(f264,plain,
    ( ~ spl4_3
    | spl4_22 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl4_3
    | spl4_22 ),
    inference(resolution,[],[f254,f113])).

fof(f113,plain,
    ( v4_lattices(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f108,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f254,plain,
    ( ~ v4_lattices(sK1)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl4_22
  <=> v4_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f262,plain,
    ( spl4_2
    | ~ spl4_22
    | ~ spl4_23
    | spl4_24
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f249,f198,f260,f256,f252,f102])).

fof(f249,plain,
    ( ! [X2,X3] :
        ( ~ r3_lattices(sK1,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | X2 = X3
        | ~ r1_lattices(sK1,X3,X2)
        | ~ l2_lattices(sK1)
        | ~ v4_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_16 ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,
    ( ! [X2,X3] :
        ( ~ r3_lattices(sK1,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | X2 = X3
        | ~ r1_lattices(sK1,X3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ l2_lattices(sK1)
        | ~ v4_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_16 ),
    inference(resolution,[],[f199,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f223,plain,
    ( spl4_2
    | ~ spl4_1
    | spl4_18
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f213,f124,f221,f98,f102])).

fof(f213,plain,
    ( ! [X0] :
        ( k4_lattices(sK1,sK3,k7_lattices(sK1,X0)) = k4_lattices(sK1,k7_lattices(sK1,X0),sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l3_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_4 ),
    inference(resolution,[],[f130,f90])).

fof(f130,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k4_lattices(sK1,sK3,X1) = k4_lattices(sK1,X1,sK3) )
    | ~ spl4_4 ),
    inference(resolution,[],[f125,f63])).

fof(f204,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl4_12 ),
    inference(resolution,[],[f177,f62])).

fof(f177,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f175])).

fof(f202,plain,
    ( ~ spl4_3
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl4_3
    | spl4_15 ),
    inference(resolution,[],[f196,f117])).

fof(f117,plain,
    ( v8_lattices(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f108,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f196,plain,
    ( ~ v8_lattices(sK1)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f194])).

fof(f200,plain,
    ( spl4_2
    | ~ spl4_8
    | ~ spl4_15
    | ~ spl4_1
    | spl4_16
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f192,f106,f198,f98,f194,f147,f102])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l3_lattices(sK1)
        | r1_lattices(sK1,X0,X1)
        | ~ v8_lattices(sK1)
        | ~ v6_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f91,f118])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f191,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl4_11 ),
    inference(resolution,[],[f173,f60])).

fof(f173,plain,
    ( ~ v17_lattices(sK1)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f171])).

fof(f189,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f169,f59])).

fof(f59,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f169,plain,
    ( ~ v10_lattices(sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f167])).

fof(f158,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl4_5 ),
    inference(resolution,[],[f154,f61])).

fof(f154,plain,
    ( ~ l3_lattices(sK1)
    | spl4_5 ),
    inference(resolution,[],[f137,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f137,plain,
    ( ~ l1_lattices(sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f156,plain,
    ( ~ spl4_3
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl4_3
    | spl4_8 ),
    inference(resolution,[],[f149,f115])).

fof(f115,plain,
    ( v6_lattices(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f108,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f149,plain,
    ( ~ v6_lattices(sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f128,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl4_2 ),
    inference(resolution,[],[f104,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f104,plain,
    ( v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f126,plain,
    ( ~ spl4_1
    | spl4_2
    | spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f122,f106,f124,f102,f98])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k4_lattices(sK1,X0,X1) = k4_lattices(sK1,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ l3_lattices(sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f121,f115])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f95,f66])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f111,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f100,f61])).

fof(f100,plain,
    ( ~ l3_lattices(sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f109,plain,
    ( ~ spl4_1
    | spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f96,f106,f102,f98])).

fof(f96,plain,
    ( sP0(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1) ),
    inference(resolution,[],[f82,f59])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | sP0(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f26,f49])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

%------------------------------------------------------------------------------
