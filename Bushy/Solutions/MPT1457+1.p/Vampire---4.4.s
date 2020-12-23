%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t52_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:10 EDT 2019

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  577 (2512 expanded)
%              Number of leaves         :  140 (1091 expanded)
%              Depth                    :   14
%              Number of atoms          : 2422 (8504 expanded)
%              Number of equality atoms :  190 ( 836 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f182,f189,f196,f203,f210,f217,f224,f231,f238,f245,f254,f261,f270,f277,f287,f297,f307,f314,f321,f329,f336,f349,f356,f368,f389,f397,f428,f443,f467,f474,f491,f502,f511,f522,f524,f526,f544,f546,f548,f558,f610,f617,f653,f660,f667,f720,f727,f760,f767,f802,f809,f816,f823,f856,f863,f870,f877,f884,f917,f924,f931,f938,f1350,f1357,f1529,f1536,f2637,f2644,f2651,f2658,f2994,f3001,f7326,f7333,f7340,f7347,f7354,f8116,f8123,f8130,f8137,f8144,f8152,f8159,f8166,f8173,f9657,f9694,f9701,f9708,f9715,f9722,f9729,f9736,f9743,f9750,f9757,f9764,f9771,f9780,f10177,f10219,f10655,f10748])).

fof(f10748,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112
    | spl7_165 ),
    inference(avatar_contradiction_clause,[],[f10747])).

fof(f10747,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112
    | ~ spl7_165 ),
    inference(subsumption_resolution,[],[f10746,f9650])).

fof(f9650,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl7_165 ),
    inference(avatar_component_clause,[],[f9649])).

fof(f9649,plain,
    ( spl7_165
  <=> k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_165])])).

fof(f10746,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112 ),
    inference(backward_demodulation,[],[f10745,f8071])).

fof(f8071,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f8070,f8045])).

fof(f8045,plain,
    ( k4_lattices(sK0,k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)),k3_lattices(sK0,sK1,sK2)) = k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_74
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f7466,f7123])).

fof(f7123,plain,
    ( k4_filter_0(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,sK1,sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_74
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f7122,f4322])).

fof(f4322,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1)
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f181,f348,f269,f237,f244,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',commutativity_k3_lattices)).

fof(f244,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl7_18
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f237,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl7_16
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f269,plain,
    ( l2_lattices(sK0)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl7_24
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f348,plain,
    ( v4_lattices(sK0)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl7_42
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f181,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f7122,plain,
    ( k4_filter_0(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,sK2,sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_74
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f7037,f766])).

fof(f766,plain,
    ( k7_lattices(sK0,k7_lattices(sK0,sK2)) = sK2
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f765])).

fof(f765,plain,
    ( spl7_88
  <=> k7_lattices(sK0,k7_lattices(sK0,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f7037,plain,
    ( k4_filter_0(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f616,f237,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k4_filter_0(X0,X1,X2) = k3_lattices(X0,k7_lattices(X0,X1),X2)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_filter_0(X0,X1,X2) = k3_lattices(X0,k7_lattices(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_filter_0(X0,X1,X2) = k3_lattices(X0,k7_lattices(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k4_filter_0(X0,X1,X2) = k3_lattices(X0,k7_lattices(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',t55_filter_0)).

fof(f616,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f615])).

fof(f615,plain,
    ( spl7_74
  <=> m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f202,plain,
    ( l3_lattices(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl7_6
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f195,plain,
    ( v17_lattices(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl7_4
  <=> v17_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f188,plain,
    ( v10_lattices(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl7_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f7466,plain,
    ( k4_lattices(sK0,k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)),k4_filter_0(sK0,k7_lattices(sK0,sK2),sK1)) = k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f181,f188,f202,f237,f616,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1)) = k7_filter_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1)) = k7_filter_0(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1)) = k7_filter_0(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1)) = k7_filter_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',d11_filter_0)).

fof(f8070,plain,
    ( k4_lattices(sK0,k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)),k3_lattices(sK0,sK1,sK2)) = k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86 ),
    inference(forward_demodulation,[],[f8069,f7259])).

fof(f7259,plain,
    ( k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k4_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(forward_demodulation,[],[f6821,f7250])).

fof(f7250,plain,
    ( k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(backward_demodulation,[],[f6839,f4169])).

fof(f4169,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f181,f348,f269,f609,f616,f164])).

fof(f609,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f608])).

fof(f608,plain,
    ( spl7_72
  <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f6839,plain,
    ( k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f237,f616,f147])).

fof(f6821,plain,
    ( k4_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f244,f609,f147])).

fof(f8069,plain,
    ( k4_lattices(sK0,k4_filter_0(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK1,sK2)) = k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_72
    | ~ spl7_86 ),
    inference(forward_demodulation,[],[f7448,f7112])).

fof(f7112,plain,
    ( k4_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,sK1,sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_72
    | ~ spl7_86 ),
    inference(forward_demodulation,[],[f7055,f759])).

fof(f759,plain,
    ( k7_lattices(sK0,k7_lattices(sK0,sK1)) = sK1
    | ~ spl7_86 ),
    inference(avatar_component_clause,[],[f758])).

fof(f758,plain,
    ( spl7_86
  <=> k7_lattices(sK0,k7_lattices(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f7055,plain,
    ( k4_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f609,f244,f147])).

fof(f7448,plain,
    ( k4_lattices(sK0,k4_filter_0(sK0,sK2,k7_lattices(sK0,sK1)),k4_filter_0(sK0,k7_lattices(sK0,sK1),sK2)) = k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f181,f188,f202,f244,f609,f151])).

fof(f10745,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112 ),
    inference(forward_demodulation,[],[f10744,f8887])).

fof(f8887,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)),k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_110
    | ~ spl7_112 ),
    inference(forward_demodulation,[],[f8211,f7722])).

fof(f7722,plain,
    ( k4_lattices(sK0,k4_filter_0(sK0,sK2,sK1),k4_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,sK1,sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_110
    | ~ spl7_112 ),
    inference(backward_demodulation,[],[f7694,f2686])).

fof(f2686,plain,
    ( k4_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK2,sK1)) = k4_lattices(sK0,k4_filter_0(sK0,sK2,sK1),k4_filter_0(sK0,sK1,sK2))
    | ~ spl7_1
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_110
    | ~ spl7_112 ),
    inference(unit_resulting_resolution,[],[f181,f355,f253,f923,f930,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',commutativity_k4_lattices)).

fof(f930,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_112 ),
    inference(avatar_component_clause,[],[f929])).

fof(f929,plain,
    ( spl7_112
  <=> m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f923,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl7_110 ),
    inference(avatar_component_clause,[],[f922])).

fof(f922,plain,
    ( spl7_110
  <=> m1_subset_1(k4_filter_0(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f253,plain,
    ( l1_lattices(sK0)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl7_20
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f355,plain,
    ( v6_lattices(sK0)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl7_44
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f7694,plain,
    ( k4_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK2,sK1)) = k7_filter_0(sK0,sK1,sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f181,f188,f202,f237,f244,f151])).

fof(f8211,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,k4_filter_0(sK0,sK2,sK1),k4_filter_0(sK0,sK1,sK2))) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)),k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_110
    | ~ spl7_112 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f923,f930,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',t50_lattices)).

fof(f10744,plain,
    ( k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)),k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f10743,f9368])).

fof(f9368,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_74
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f9367,f7049])).

fof(f7049,plain,
    ( k4_filter_0(sK0,sK2,sK1) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f244,f237,f147])).

fof(f9367,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_74
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f9248,f766])).

fof(f9248,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f616,f237,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',t51_lattices)).

fof(f10743,plain,
    ( k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86 ),
    inference(forward_demodulation,[],[f10742,f9344])).

fof(f9344,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86 ),
    inference(backward_demodulation,[],[f9341,f2794])).

fof(f2794,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f181,f355,f253,f616,f237,f163])).

fof(f9341,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_72
    | ~ spl7_86 ),
    inference(forward_demodulation,[],[f9340,f7067])).

fof(f7067,plain,
    ( k4_filter_0(sK0,sK1,sK2) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f237,f244,f147])).

fof(f9340,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_72
    | ~ spl7_86 ),
    inference(forward_demodulation,[],[f9265,f759])).

fof(f9265,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK2)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f609,f244,f149])).

fof(f10742,plain,
    ( k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK2),sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_72
    | ~ spl7_86 ),
    inference(forward_demodulation,[],[f9869,f759])).

fof(f9869,plain,
    ( k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK1))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f244,f609,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k7_filter_0(X0,X1,X2) = k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_filter_0(X0,X1,X2) = k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_filter_0(X0,X1,X2) = k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_filter_0(X0,X1,X2) = k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',t51_filter_1)).

fof(f10655,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112
    | spl7_165 ),
    inference(avatar_contradiction_clause,[],[f10654])).

fof(f10654,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112
    | ~ spl7_165 ),
    inference(subsumption_resolution,[],[f10653,f9650])).

fof(f10653,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112 ),
    inference(forward_demodulation,[],[f10652,f8902])).

fof(f8902,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)),k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_110
    | ~ spl7_112 ),
    inference(forward_demodulation,[],[f8194,f7694])).

fof(f8194,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK2,sK1))) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)),k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_110
    | ~ spl7_112 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f930,f923,f148])).

fof(f10652,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)),k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f10651,f9341])).

fof(f10651,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f10650,f9372])).

fof(f9372,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_88 ),
    inference(backward_demodulation,[],[f9368,f2806])).

fof(f2806,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f181,f355,f253,f609,f244,f163])).

fof(f10650,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_74
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f9886,f766])).

fof(f9886,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f237,f616,f150])).

fof(f10219,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112
    | spl7_167 ),
    inference(avatar_contradiction_clause,[],[f10218])).

fof(f10218,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112
    | ~ spl7_167 ),
    inference(subsumption_resolution,[],[f10217,f9656])).

fof(f9656,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | ~ spl7_167 ),
    inference(avatar_component_clause,[],[f9655])).

fof(f9655,plain,
    ( spl7_167
  <=> k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_167])])).

fof(f10217,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112 ),
    inference(backward_demodulation,[],[f10216,f7992])).

fof(f7992,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k7_filter_0(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f7991,f7727])).

fof(f7727,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2))) = k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86 ),
    inference(forward_demodulation,[],[f7726,f7112])).

fof(f7726,plain,
    ( k4_lattices(sK0,k4_filter_0(sK0,k7_lattices(sK0,sK1),sK2),k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2))) = k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(forward_demodulation,[],[f7682,f7259])).

fof(f7682,plain,
    ( k4_lattices(sK0,k4_filter_0(sK0,k7_lattices(sK0,sK1),sK2),k4_filter_0(sK0,sK2,k7_lattices(sK0,sK1))) = k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f181,f188,f202,f609,f244,f151])).

fof(f7991,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2))) = k7_filter_0(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42
    | ~ spl7_74
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f7664,f7123])).

fof(f7664,plain,
    ( k4_lattices(sK0,k4_filter_0(sK0,k7_lattices(sK0,sK2),sK1),k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2))) = k7_filter_0(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f181,f188,f202,f616,f237,f151])).

fof(f10216,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112 ),
    inference(forward_demodulation,[],[f10215,f8902])).

fof(f10215,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)),k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f10214,f9344])).

fof(f10214,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_74
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f10213,f9368])).

fof(f10213,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_74
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f10056,f766])).

fof(f10056,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f616,f237,f150])).

fof(f10177,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112
    | spl7_167 ),
    inference(avatar_contradiction_clause,[],[f10176])).

fof(f10176,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112
    | ~ spl7_167 ),
    inference(subsumption_resolution,[],[f10175,f9656])).

fof(f10175,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112 ),
    inference(forward_demodulation,[],[f10174,f8887])).

fof(f10174,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)),k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f10173,f9372])).

fof(f10173,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),sK2),k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_72
    | ~ spl7_86 ),
    inference(forward_demodulation,[],[f10172,f9341])).

fof(f10172,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),sK2),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_72
    | ~ spl7_86 ),
    inference(forward_demodulation,[],[f10073,f759])).

fof(f10073,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),sK2),k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK2)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f609,f244,f150])).

fof(f9780,plain,
    ( ~ spl7_193
    | ~ spl7_162 ),
    inference(avatar_split_clause,[],[f9681,f8171,f9778])).

fof(f9778,plain,
    ( spl7_193
  <=> ~ r2_hidden(u1_struct_0(sK0),k4_lattices(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_193])])).

fof(f8171,plain,
    ( spl7_162
  <=> r2_hidden(k4_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).

fof(f9681,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k4_lattices(sK0,sK2,sK2))
    | ~ spl7_162 ),
    inference(unit_resulting_resolution,[],[f8172,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',antisymmetry_r2_hidden)).

fof(f8172,plain,
    ( r2_hidden(k4_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_162 ),
    inference(avatar_component_clause,[],[f8171])).

fof(f9771,plain,
    ( ~ spl7_191
    | ~ spl7_160 ),
    inference(avatar_split_clause,[],[f9671,f8164,f9769])).

fof(f9769,plain,
    ( spl7_191
  <=> ~ r2_hidden(u1_struct_0(sK0),k4_lattices(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_191])])).

fof(f8164,plain,
    ( spl7_160
  <=> r2_hidden(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_160])])).

fof(f9671,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k4_lattices(sK0,sK1,sK2))
    | ~ spl7_160 ),
    inference(unit_resulting_resolution,[],[f8165,f153])).

fof(f8165,plain,
    ( r2_hidden(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_160 ),
    inference(avatar_component_clause,[],[f8164])).

fof(f9764,plain,
    ( ~ spl7_189
    | ~ spl7_158 ),
    inference(avatar_split_clause,[],[f9661,f8157,f9762])).

fof(f9762,plain,
    ( spl7_189
  <=> ~ r2_hidden(u1_struct_0(sK0),k4_lattices(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_189])])).

fof(f8157,plain,
    ( spl7_158
  <=> r2_hidden(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_158])])).

fof(f9661,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k4_lattices(sK0,sK1,sK1))
    | ~ spl7_158 ),
    inference(unit_resulting_resolution,[],[f8158,f153])).

fof(f8158,plain,
    ( r2_hidden(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_158 ),
    inference(avatar_component_clause,[],[f8157])).

fof(f9757,plain,
    ( ~ spl7_187
    | ~ spl7_156 ),
    inference(avatar_split_clause,[],[f9638,f8150,f9755])).

fof(f9755,plain,
    ( spl7_187
  <=> ~ r2_hidden(u1_struct_0(sK0),k3_lattices(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_187])])).

fof(f8150,plain,
    ( spl7_156
  <=> r2_hidden(k3_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_156])])).

fof(f9638,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k3_lattices(sK0,sK2,sK2))
    | ~ spl7_156 ),
    inference(unit_resulting_resolution,[],[f8151,f153])).

fof(f8151,plain,
    ( r2_hidden(k3_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_156 ),
    inference(avatar_component_clause,[],[f8150])).

fof(f9750,plain,
    ( ~ spl7_185
    | ~ spl7_154 ),
    inference(avatar_split_clause,[],[f9628,f8142,f9748])).

fof(f9748,plain,
    ( spl7_185
  <=> ~ r2_hidden(u1_struct_0(sK0),k3_lattices(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_185])])).

fof(f8142,plain,
    ( spl7_154
  <=> r2_hidden(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).

fof(f9628,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k3_lattices(sK0,sK1,sK2))
    | ~ spl7_154 ),
    inference(unit_resulting_resolution,[],[f8143,f153])).

fof(f8143,plain,
    ( r2_hidden(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_154 ),
    inference(avatar_component_clause,[],[f8142])).

fof(f9743,plain,
    ( ~ spl7_183
    | ~ spl7_152 ),
    inference(avatar_split_clause,[],[f9618,f8135,f9741])).

fof(f9741,plain,
    ( spl7_183
  <=> ~ r2_hidden(u1_struct_0(sK0),k3_lattices(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_183])])).

fof(f8135,plain,
    ( spl7_152
  <=> r2_hidden(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_152])])).

fof(f9618,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k3_lattices(sK0,sK1,sK1))
    | ~ spl7_152 ),
    inference(unit_resulting_resolution,[],[f8136,f153])).

fof(f8136,plain,
    ( r2_hidden(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_152 ),
    inference(avatar_component_clause,[],[f8135])).

fof(f9736,plain,
    ( ~ spl7_181
    | ~ spl7_150 ),
    inference(avatar_split_clause,[],[f9608,f8128,f9734])).

fof(f9734,plain,
    ( spl7_181
  <=> ~ r2_hidden(u1_struct_0(sK0),k7_filter_0(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_181])])).

fof(f8128,plain,
    ( spl7_150
  <=> r2_hidden(k7_filter_0(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).

fof(f9608,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k7_filter_0(sK0,sK2,sK2))
    | ~ spl7_150 ),
    inference(unit_resulting_resolution,[],[f8129,f153])).

fof(f8129,plain,
    ( r2_hidden(k7_filter_0(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_150 ),
    inference(avatar_component_clause,[],[f8128])).

fof(f9729,plain,
    ( ~ spl7_179
    | ~ spl7_148 ),
    inference(avatar_split_clause,[],[f9598,f8121,f9727])).

fof(f9727,plain,
    ( spl7_179
  <=> ~ r2_hidden(u1_struct_0(sK0),k7_filter_0(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_179])])).

fof(f8121,plain,
    ( spl7_148
  <=> r2_hidden(k7_filter_0(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_148])])).

fof(f9598,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k7_filter_0(sK0,sK1,sK2))
    | ~ spl7_148 ),
    inference(unit_resulting_resolution,[],[f8122,f153])).

fof(f8122,plain,
    ( r2_hidden(k7_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_148 ),
    inference(avatar_component_clause,[],[f8121])).

fof(f9722,plain,
    ( ~ spl7_177
    | ~ spl7_146 ),
    inference(avatar_split_clause,[],[f8966,f8114,f9720])).

fof(f9720,plain,
    ( spl7_177
  <=> ~ r2_hidden(u1_struct_0(sK0),k7_filter_0(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_177])])).

fof(f8114,plain,
    ( spl7_146
  <=> r2_hidden(k7_filter_0(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_146])])).

fof(f8966,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k7_filter_0(sK0,sK1,sK1))
    | ~ spl7_146 ),
    inference(unit_resulting_resolution,[],[f8115,f153])).

fof(f8115,plain,
    ( r2_hidden(k7_filter_0(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_146 ),
    inference(avatar_component_clause,[],[f8114])).

fof(f9715,plain,
    ( ~ spl7_175
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f8956,f7352,f9713])).

fof(f9713,plain,
    ( spl7_175
  <=> ~ r2_hidden(u1_struct_0(sK0),k4_filter_0(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_175])])).

fof(f7352,plain,
    ( spl7_144
  <=> r2_hidden(k4_filter_0(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).

fof(f8956,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k4_filter_0(sK0,sK2,sK2))
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f7353,f153])).

fof(f7353,plain,
    ( r2_hidden(k4_filter_0(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_144 ),
    inference(avatar_component_clause,[],[f7352])).

fof(f9708,plain,
    ( ~ spl7_173
    | ~ spl7_142 ),
    inference(avatar_split_clause,[],[f8946,f7345,f9706])).

fof(f9706,plain,
    ( spl7_173
  <=> ~ r2_hidden(u1_struct_0(sK0),k4_filter_0(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_173])])).

fof(f7345,plain,
    ( spl7_142
  <=> r2_hidden(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).

fof(f8946,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k4_filter_0(sK0,sK1,sK2))
    | ~ spl7_142 ),
    inference(unit_resulting_resolution,[],[f7346,f153])).

fof(f7346,plain,
    ( r2_hidden(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_142 ),
    inference(avatar_component_clause,[],[f7345])).

fof(f9701,plain,
    ( ~ spl7_171
    | ~ spl7_140 ),
    inference(avatar_split_clause,[],[f8936,f7338,f9699])).

fof(f9699,plain,
    ( spl7_171
  <=> ~ r2_hidden(u1_struct_0(sK0),k4_filter_0(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_171])])).

fof(f7338,plain,
    ( spl7_140
  <=> r2_hidden(k4_filter_0(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).

fof(f8936,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k4_filter_0(sK0,sK2,sK1))
    | ~ spl7_140 ),
    inference(unit_resulting_resolution,[],[f7339,f153])).

fof(f7339,plain,
    ( r2_hidden(k4_filter_0(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl7_140 ),
    inference(avatar_component_clause,[],[f7338])).

fof(f9694,plain,
    ( ~ spl7_169
    | ~ spl7_138 ),
    inference(avatar_split_clause,[],[f8926,f7331,f9692])).

fof(f9692,plain,
    ( spl7_169
  <=> ~ r2_hidden(u1_struct_0(sK0),k4_filter_0(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_169])])).

fof(f7331,plain,
    ( spl7_138
  <=> r2_hidden(k4_filter_0(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_138])])).

fof(f8926,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k4_filter_0(sK0,sK1,sK1))
    | ~ spl7_138 ),
    inference(unit_resulting_resolution,[],[f7332,f153])).

fof(f7332,plain,
    ( r2_hidden(k4_filter_0(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_138 ),
    inference(avatar_component_clause,[],[f7331])).

fof(f9657,plain,
    ( ~ spl7_165
    | ~ spl7_167
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112 ),
    inference(avatar_split_clause,[],[f9375,f929,f922,f765,f758,f615,f608,f354,f252,f243,f236,f201,f194,f187,f180,f9655,f9649])).

fof(f9375,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88
    | ~ spl7_110
    | ~ spl7_112 ),
    inference(subsumption_resolution,[],[f9369,f8902])).

fof(f9369,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)),k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)))
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_86
    | ~ spl7_88 ),
    inference(backward_demodulation,[],[f9368,f9348])).

fof(f9348,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)),k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_86 ),
    inference(subsumption_resolution,[],[f9345,f9341])).

fof(f9345,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)),k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72
    | ~ spl7_86 ),
    inference(backward_demodulation,[],[f9341,f2867])).

fof(f2867,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_72 ),
    inference(backward_demodulation,[],[f2806,f132])).

fof(f132,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK2))
    | k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,
    ( ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
      | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
      | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK2))
      | k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f60,f116,f115,f114])).

fof(f114,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k7_filter_0(X0,k7_lattices(X0,X1),X2)
                  | k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k7_filter_0(X0,X1,k7_lattices(X0,X2))
                  | k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k3_lattices(X0,k4_lattices(X0,X1,k7_lattices(X0,X2)),k4_lattices(X0,k7_lattices(X0,X1),X2))
                  | k7_lattices(X0,k4_filter_0(X0,X1,X2)) != k4_lattices(X0,X1,k7_lattices(X0,X2)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k7_lattices(sK0,k7_filter_0(sK0,X1,X2)) != k7_filter_0(sK0,k7_lattices(sK0,X1),X2)
                | k7_lattices(sK0,k7_filter_0(sK0,X1,X2)) != k7_filter_0(sK0,X1,k7_lattices(sK0,X2))
                | k7_lattices(sK0,k7_filter_0(sK0,X1,X2)) != k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,X2)),k4_lattices(sK0,k7_lattices(sK0,X1),X2))
                | k7_lattices(sK0,k4_filter_0(sK0,X1,X2)) != k4_lattices(sK0,X1,k7_lattices(sK0,X2)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f115,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k7_filter_0(X0,k7_lattices(X0,X1),X2)
                | k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k7_filter_0(X0,X1,k7_lattices(X0,X2))
                | k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k3_lattices(X0,k4_lattices(X0,X1,k7_lattices(X0,X2)),k4_lattices(X0,k7_lattices(X0,X1),X2))
                | k7_lattices(X0,k4_filter_0(X0,X1,X2)) != k4_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( k7_lattices(X0,k7_filter_0(X0,sK1,X2)) != k7_filter_0(X0,k7_lattices(X0,sK1),X2)
              | k7_lattices(X0,k7_filter_0(X0,sK1,X2)) != k7_filter_0(X0,sK1,k7_lattices(X0,X2))
              | k7_lattices(X0,k7_filter_0(X0,sK1,X2)) != k3_lattices(X0,k4_lattices(X0,sK1,k7_lattices(X0,X2)),k4_lattices(X0,k7_lattices(X0,sK1),X2))
              | k7_lattices(X0,k4_filter_0(X0,sK1,X2)) != k4_lattices(X0,sK1,k7_lattices(X0,X2)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k7_filter_0(X0,k7_lattices(X0,X1),X2)
            | k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k7_filter_0(X0,X1,k7_lattices(X0,X2))
            | k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k3_lattices(X0,k4_lattices(X0,X1,k7_lattices(X0,X2)),k4_lattices(X0,k7_lattices(X0,X1),X2))
            | k7_lattices(X0,k4_filter_0(X0,X1,X2)) != k4_lattices(X0,X1,k7_lattices(X0,X2)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k7_lattices(X0,k7_filter_0(X0,X1,sK2)) != k7_filter_0(X0,k7_lattices(X0,X1),sK2)
          | k7_lattices(X0,k7_filter_0(X0,X1,sK2)) != k7_filter_0(X0,X1,k7_lattices(X0,sK2))
          | k7_lattices(X0,k7_filter_0(X0,X1,sK2)) != k3_lattices(X0,k4_lattices(X0,X1,k7_lattices(X0,sK2)),k4_lattices(X0,k7_lattices(X0,X1),sK2))
          | k7_lattices(X0,k4_filter_0(X0,X1,sK2)) != k4_lattices(X0,X1,k7_lattices(X0,sK2)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k7_filter_0(X0,k7_lattices(X0,X1),X2)
                | k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k7_filter_0(X0,X1,k7_lattices(X0,X2))
                | k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k3_lattices(X0,k4_lattices(X0,X1,k7_lattices(X0,X2)),k4_lattices(X0,k7_lattices(X0,X1),X2))
                | k7_lattices(X0,k4_filter_0(X0,X1,X2)) != k4_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k7_filter_0(X0,k7_lattices(X0,X1),X2)
                | k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k7_filter_0(X0,X1,k7_lattices(X0,X2))
                | k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k3_lattices(X0,k4_lattices(X0,X1,k7_lattices(X0,X2)),k4_lattices(X0,k7_lattices(X0,X1),X2))
                | k7_lattices(X0,k4_filter_0(X0,X1,X2)) != k4_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k7_lattices(X0,k7_filter_0(X0,X1,X2)) = k7_filter_0(X0,k7_lattices(X0,X1),X2)
                  & k7_lattices(X0,k7_filter_0(X0,X1,X2)) = k7_filter_0(X0,X1,k7_lattices(X0,X2))
                  & k7_lattices(X0,k7_filter_0(X0,X1,X2)) = k3_lattices(X0,k4_lattices(X0,X1,k7_lattices(X0,X2)),k4_lattices(X0,k7_lattices(X0,X1),X2))
                  & k7_lattices(X0,k4_filter_0(X0,X1,X2)) = k4_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k7_lattices(X0,k7_filter_0(X0,X1,X2)) = k7_filter_0(X0,k7_lattices(X0,X1),X2)
                & k7_lattices(X0,k7_filter_0(X0,X1,X2)) = k7_filter_0(X0,X1,k7_lattices(X0,X2))
                & k7_lattices(X0,k7_filter_0(X0,X1,X2)) = k3_lattices(X0,k4_lattices(X0,X1,k7_lattices(X0,X2)),k4_lattices(X0,k7_lattices(X0,X1),X2))
                & k7_lattices(X0,k4_filter_0(X0,X1,X2)) = k4_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',t52_filter_1)).

fof(f8173,plain,
    ( spl7_162
    | spl7_57
    | ~ spl7_134 ),
    inference(avatar_split_clause,[],[f6579,f2999,f441,f8171])).

fof(f441,plain,
    ( spl7_57
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f2999,plain,
    ( spl7_134
  <=> m1_subset_1(k4_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).

fof(f6579,plain,
    ( r2_hidden(k4_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_134 ),
    inference(unit_resulting_resolution,[],[f442,f3000,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',t2_subset)).

fof(f3000,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_134 ),
    inference(avatar_component_clause,[],[f2999])).

fof(f442,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f441])).

fof(f8166,plain,
    ( spl7_160
    | spl7_57
    | ~ spl7_132 ),
    inference(avatar_split_clause,[],[f6056,f2992,f441,f8164])).

fof(f2992,plain,
    ( spl7_132
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f6056,plain,
    ( r2_hidden(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_132 ),
    inference(unit_resulting_resolution,[],[f442,f2993,f155])).

fof(f2993,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_132 ),
    inference(avatar_component_clause,[],[f2992])).

fof(f8159,plain,
    ( spl7_158
    | spl7_57
    | ~ spl7_130 ),
    inference(avatar_split_clause,[],[f5561,f2656,f441,f8157])).

fof(f2656,plain,
    ( spl7_130
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f5561,plain,
    ( r2_hidden(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_130 ),
    inference(unit_resulting_resolution,[],[f442,f2657,f155])).

fof(f2657,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_130 ),
    inference(avatar_component_clause,[],[f2656])).

fof(f8152,plain,
    ( spl7_156
    | spl7_57
    | ~ spl7_128 ),
    inference(avatar_split_clause,[],[f5094,f2649,f441,f8150])).

fof(f2649,plain,
    ( spl7_128
  <=> m1_subset_1(k3_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f5094,plain,
    ( r2_hidden(k3_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_128 ),
    inference(unit_resulting_resolution,[],[f442,f2650,f155])).

fof(f2650,plain,
    ( m1_subset_1(k3_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_128 ),
    inference(avatar_component_clause,[],[f2649])).

fof(f8144,plain,
    ( spl7_154
    | spl7_57
    | ~ spl7_126 ),
    inference(avatar_split_clause,[],[f3991,f2642,f441,f8142])).

fof(f2642,plain,
    ( spl7_126
  <=> m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_126])])).

fof(f3991,plain,
    ( r2_hidden(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_126 ),
    inference(unit_resulting_resolution,[],[f442,f2643,f155])).

fof(f2643,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_126 ),
    inference(avatar_component_clause,[],[f2642])).

fof(f8137,plain,
    ( spl7_152
    | spl7_57
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f3257,f882,f441,f8135])).

fof(f882,plain,
    ( spl7_106
  <=> m1_subset_1(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f3257,plain,
    ( r2_hidden(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f442,f883,f155])).

fof(f883,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_106 ),
    inference(avatar_component_clause,[],[f882])).

fof(f8130,plain,
    ( spl7_150
    | spl7_57
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f2579,f1534,f441,f8128])).

fof(f1534,plain,
    ( spl7_122
  <=> m1_subset_1(k7_filter_0(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).

fof(f2579,plain,
    ( r2_hidden(k7_filter_0(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(unit_resulting_resolution,[],[f442,f1535,f155])).

fof(f1535,plain,
    ( m1_subset_1(k7_filter_0(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_122 ),
    inference(avatar_component_clause,[],[f1534])).

fof(f8123,plain,
    ( spl7_148
    | spl7_57
    | ~ spl7_120 ),
    inference(avatar_split_clause,[],[f2052,f1527,f441,f8121])).

fof(f1527,plain,
    ( spl7_120
  <=> m1_subset_1(k7_filter_0(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f2052,plain,
    ( r2_hidden(k7_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_120 ),
    inference(unit_resulting_resolution,[],[f442,f1528,f155])).

fof(f1528,plain,
    ( m1_subset_1(k7_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_120 ),
    inference(avatar_component_clause,[],[f1527])).

fof(f8116,plain,
    ( spl7_146
    | spl7_57
    | ~ spl7_116 ),
    inference(avatar_split_clause,[],[f1680,f1348,f441,f8114])).

fof(f1348,plain,
    ( spl7_116
  <=> m1_subset_1(k7_filter_0(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).

fof(f1680,plain,
    ( r2_hidden(k7_filter_0(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_116 ),
    inference(unit_resulting_resolution,[],[f442,f1349,f155])).

fof(f1349,plain,
    ( m1_subset_1(k7_filter_0(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_116 ),
    inference(avatar_component_clause,[],[f1348])).

fof(f7354,plain,
    ( spl7_144
    | spl7_57
    | ~ spl7_114 ),
    inference(avatar_split_clause,[],[f1342,f936,f441,f7352])).

fof(f936,plain,
    ( spl7_114
  <=> m1_subset_1(k4_filter_0(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).

fof(f1342,plain,
    ( r2_hidden(k4_filter_0(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_114 ),
    inference(unit_resulting_resolution,[],[f442,f937,f155])).

fof(f937,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_114 ),
    inference(avatar_component_clause,[],[f936])).

fof(f7347,plain,
    ( spl7_142
    | spl7_57
    | ~ spl7_112 ),
    inference(avatar_split_clause,[],[f1229,f929,f441,f7345])).

fof(f1229,plain,
    ( r2_hidden(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_112 ),
    inference(unit_resulting_resolution,[],[f442,f930,f155])).

fof(f7340,plain,
    ( spl7_140
    | spl7_57
    | ~ spl7_110 ),
    inference(avatar_split_clause,[],[f1128,f922,f441,f7338])).

fof(f1128,plain,
    ( r2_hidden(k4_filter_0(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_110 ),
    inference(unit_resulting_resolution,[],[f442,f923,f155])).

fof(f7333,plain,
    ( spl7_138
    | spl7_57
    | ~ spl7_108 ),
    inference(avatar_split_clause,[],[f1002,f915,f441,f7331])).

fof(f915,plain,
    ( spl7_108
  <=> m1_subset_1(k4_filter_0(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f1002,plain,
    ( r2_hidden(k4_filter_0(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_108 ),
    inference(unit_resulting_resolution,[],[f442,f916,f155])).

fof(f916,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_108 ),
    inference(avatar_component_clause,[],[f915])).

fof(f7326,plain,
    ( ~ spl7_137
    | spl7_65 ),
    inference(avatar_split_clause,[],[f602,f500,f7324])).

fof(f7324,plain,
    ( spl7_137
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_137])])).

fof(f500,plain,
    ( spl7_65
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f602,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl7_65 ),
    inference(unit_resulting_resolution,[],[f152,f501,f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',t4_subset)).

fof(f501,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f500])).

fof(f152,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',existence_m1_subset_1)).

fof(f3001,plain,
    ( spl7_134
    | spl7_1
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f830,f354,f252,f243,f180,f2999])).

fof(f830,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f181,f355,f253,f244,f244,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',dt_k4_lattices)).

fof(f2994,plain,
    ( spl7_132
    | spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f829,f354,f252,f243,f236,f180,f2992])).

fof(f829,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f181,f355,f253,f237,f244,f160])).

fof(f2658,plain,
    ( spl7_130
    | spl7_1
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f824,f354,f252,f236,f180,f2656])).

fof(f824,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f181,f355,f253,f237,f237,f160])).

fof(f2651,plain,
    ( spl7_128
    | spl7_1
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f775,f347,f268,f243,f180,f2649])).

fof(f775,plain,
    ( m1_subset_1(k3_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f181,f348,f269,f244,f244,f159])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',dt_k3_lattices)).

fof(f2644,plain,
    ( spl7_126
    | spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f774,f347,f268,f243,f236,f180,f2642])).

fof(f774,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f181,f348,f269,f237,f244,f159])).

fof(f2637,plain,
    ( spl7_124
    | spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f770,f347,f268,f243,f236,f180,f2635])).

fof(f2635,plain,
    ( spl7_124
  <=> m1_subset_1(k3_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f770,plain,
    ( m1_subset_1(k3_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f181,f348,f269,f244,f237,f159])).

fof(f1536,plain,
    ( spl7_122
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f1032,f243,f201,f187,f180,f1534])).

fof(f1032,plain,
    ( m1_subset_1(k7_filter_0(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f181,f188,f202,f244,f244,f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f101])).

fof(f101,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_filter_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',dt_k7_filter_0)).

fof(f1529,plain,
    ( spl7_120
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f1031,f243,f236,f201,f187,f180,f1527])).

fof(f1031,plain,
    ( m1_subset_1(k7_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f181,f188,f202,f237,f244,f166])).

fof(f1357,plain,
    ( spl7_118
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f1026,f243,f236,f201,f187,f180,f1355])).

fof(f1355,plain,
    ( spl7_118
  <=> m1_subset_1(k7_filter_0(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).

fof(f1026,plain,
    ( m1_subset_1(k7_filter_0(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f181,f188,f202,f244,f237,f166])).

fof(f1350,plain,
    ( spl7_116
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f1025,f236,f201,f187,f180,f1348])).

fof(f1025,plain,
    ( m1_subset_1(k7_filter_0(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f181,f188,f202,f237,f237,f166])).

fof(f938,plain,
    ( spl7_114
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f891,f243,f201,f187,f180,f936])).

fof(f891,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f181,f188,f202,f244,f244,f165])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f99])).

fof(f99,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',dt_k4_filter_0)).

fof(f931,plain,
    ( spl7_112
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f890,f243,f236,f201,f187,f180,f929])).

fof(f890,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f181,f188,f202,f237,f244,f165])).

fof(f924,plain,
    ( spl7_110
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f886,f243,f236,f201,f187,f180,f922])).

fof(f886,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f181,f188,f202,f244,f237,f165])).

fof(f917,plain,
    ( spl7_108
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f885,f236,f201,f187,f180,f915])).

fof(f885,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f181,f188,f202,f237,f237,f165])).

fof(f884,plain,
    ( spl7_106
    | spl7_1
    | ~ spl7_16
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f769,f347,f268,f236,f180,f882])).

fof(f769,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f181,f348,f269,f237,f237,f159])).

fof(f877,plain,
    ( spl7_104
    | spl7_1
    | ~ spl7_18
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f734,f268,f243,f180,f875])).

fof(f875,plain,
    ( spl7_104
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f734,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_18
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f181,f269,f244,f244,f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',dt_k1_lattices)).

fof(f870,plain,
    ( spl7_102
    | spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f733,f268,f243,f236,f180,f868])).

fof(f868,plain,
    ( spl7_102
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f733,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f181,f269,f237,f244,f168])).

fof(f863,plain,
    ( spl7_100
    | spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f729,f268,f243,f236,f180,f861])).

fof(f861,plain,
    ( spl7_100
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f729,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f181,f269,f244,f237,f168])).

fof(f856,plain,
    ( spl7_98
    | spl7_1
    | ~ spl7_16
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f728,f268,f236,f180,f854])).

fof(f854,plain,
    ( spl7_98
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f728,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f181,f269,f237,f237,f168])).

fof(f823,plain,
    ( spl7_96
    | spl7_1
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f674,f252,f243,f180,f821])).

fof(f821,plain,
    ( spl7_96
  <=> m1_subset_1(k2_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f674,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f181,f253,f244,f244,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',dt_k2_lattices)).

fof(f816,plain,
    ( spl7_94
    | spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f673,f252,f243,f236,f180,f814])).

fof(f814,plain,
    ( spl7_94
  <=> m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f673,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f181,f253,f237,f244,f167])).

fof(f809,plain,
    ( spl7_92
    | spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f669,f252,f243,f236,f180,f807])).

fof(f807,plain,
    ( spl7_92
  <=> m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f669,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f181,f253,f244,f237,f167])).

fof(f802,plain,
    ( spl7_90
    | spl7_1
    | ~ spl7_16
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f668,f252,f236,f180,f800])).

fof(f800,plain,
    ( spl7_90
  <=> m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f668,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f181,f253,f237,f237,f167])).

fof(f767,plain,
    ( spl7_88
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f623,f243,f201,f194,f187,f180,f765])).

fof(f623,plain,
    ( k7_lattices(sK0,k7_lattices(sK0,sK2)) = sK2
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f244,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k7_lattices(X0,k7_lattices(X0,X1)) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',t49_lattices)).

fof(f760,plain,
    ( spl7_86
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f622,f236,f201,f194,f187,f180,f758])).

fof(f622,plain,
    ( k7_lattices(sK0,k7_lattices(sK0,sK1)) = sK1
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f181,f188,f195,f202,f237,f146])).

fof(f727,plain,
    ( ~ spl7_85
    | ~ spl7_80 ),
    inference(avatar_split_clause,[],[f707,f665,f725])).

fof(f725,plain,
    ( spl7_85
  <=> ~ r2_hidden(u1_struct_0(sK0),k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f665,plain,
    ( spl7_80
  <=> r2_hidden(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f707,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k7_lattices(sK0,sK2))
    | ~ spl7_80 ),
    inference(unit_resulting_resolution,[],[f666,f153])).

fof(f666,plain,
    ( r2_hidden(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl7_80 ),
    inference(avatar_component_clause,[],[f665])).

fof(f720,plain,
    ( ~ spl7_83
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f697,f658,f718])).

fof(f718,plain,
    ( spl7_83
  <=> ~ r2_hidden(u1_struct_0(sK0),k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f658,plain,
    ( spl7_78
  <=> r2_hidden(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f697,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k7_lattices(sK0,sK1))
    | ~ spl7_78 ),
    inference(unit_resulting_resolution,[],[f659,f153])).

fof(f659,plain,
    ( r2_hidden(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f658])).

fof(f667,plain,
    ( spl7_80
    | spl7_57
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f634,f615,f441,f665])).

fof(f634,plain,
    ( r2_hidden(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f442,f616,f155])).

fof(f660,plain,
    ( spl7_78
    | spl7_57
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f620,f608,f441,f658])).

fof(f620,plain,
    ( r2_hidden(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl7_57
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f442,f609,f155])).

fof(f653,plain,
    ( ~ spl7_77
    | ~ spl7_8
    | spl7_53 ),
    inference(avatar_split_clause,[],[f570,f417,f208,f651])).

fof(f651,plain,
    ( spl7_77
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f208,plain,
    ( spl7_8
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f417,plain,
    ( spl7_53
  <=> u1_struct_0(sK0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f570,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(u1_struct_0(sK0)))
    | ~ spl7_8
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f418,f408])).

fof(f408,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK3(X5))
        | o_0_0_xboole_0 = X5 )
    | ~ spl7_8 ),
    inference(resolution,[],[f402,f153])).

fof(f402,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl7_8 ),
    inference(resolution,[],[f359,f152])).

fof(f359,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,X4)
        | r2_hidden(X3,X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl7_8 ),
    inference(resolution,[],[f155,f280])).

fof(f280,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f278,f134])).

fof(f134,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',t6_boole)).

fof(f278,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f209,f134])).

fof(f209,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f208])).

fof(f418,plain,
    ( u1_struct_0(sK0) != o_0_0_xboole_0
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f417])).

fof(f617,plain,
    ( spl7_74
    | spl7_1
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f599,f243,f201,f180,f615])).

fof(f599,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f181,f202,f244,f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',dt_k7_lattices)).

fof(f610,plain,
    ( spl7_72
    | spl7_1
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f598,f236,f201,f180,f608])).

fof(f598,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f181,f202,f237,f156])).

fof(f558,plain,
    ( spl7_70
    | ~ spl7_16
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f527,f420,f236,f556])).

fof(f556,plain,
    ( spl7_70
  <=> m1_subset_1(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f420,plain,
    ( spl7_52
  <=> u1_struct_0(sK0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f527,plain,
    ( m1_subset_1(sK1,o_0_0_xboole_0)
    | ~ spl7_16
    | ~ spl7_52 ),
    inference(backward_demodulation,[],[f421,f237])).

fof(f421,plain,
    ( u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f420])).

fof(f548,plain,
    ( ~ spl7_8
    | ~ spl7_52
    | ~ spl7_58 ),
    inference(avatar_contradiction_clause,[],[f547])).

fof(f547,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_52
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f537,f209])).

fof(f537,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_52
    | ~ spl7_58 ),
    inference(backward_demodulation,[],[f421,f484])).

fof(f484,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_58 ),
    inference(resolution,[],[f466,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',t7_boole)).

fof(f466,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f465])).

fof(f465,plain,
    ( spl7_58
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f546,plain,
    ( ~ spl7_8
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_58 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f534,f396])).

fof(f396,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl7_50
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f534,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_8
    | ~ spl7_52
    | ~ spl7_58 ),
    inference(backward_demodulation,[],[f421,f475])).

fof(f475,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_8
    | ~ spl7_58 ),
    inference(unit_resulting_resolution,[],[f209,f466,f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',t5_subset)).

fof(f544,plain,
    ( ~ spl7_8
    | ~ spl7_52
    | ~ spl7_58 ),
    inference(avatar_contradiction_clause,[],[f543])).

fof(f543,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_52
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f532,f322])).

fof(f322,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f209,f158])).

fof(f532,plain,
    ( r2_hidden(sK2,o_0_0_xboole_0)
    | ~ spl7_52
    | ~ spl7_58 ),
    inference(backward_demodulation,[],[f421,f466])).

fof(f526,plain,
    ( ~ spl7_56
    | ~ spl7_58 ),
    inference(avatar_contradiction_clause,[],[f525])).

fof(f525,plain,
    ( $false
    | ~ spl7_56
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f439,f484])).

fof(f439,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl7_56
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f524,plain,
    ( ~ spl7_8
    | ~ spl7_58
    | ~ spl7_64 ),
    inference(avatar_contradiction_clause,[],[f523])).

fof(f523,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_58
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f498,f475])).

fof(f498,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl7_64
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f522,plain,
    ( spl7_68
    | ~ spl7_8
    | spl7_53 ),
    inference(avatar_split_clause,[],[f434,f417,f208,f520])).

fof(f520,plain,
    ( spl7_68
  <=> r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f434,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_8
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f152,f418,f359])).

fof(f511,plain,
    ( ~ spl7_67
    | spl7_65 ),
    inference(avatar_split_clause,[],[f504,f500,f509])).

fof(f509,plain,
    ( spl7_67
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f504,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_65 ),
    inference(unit_resulting_resolution,[],[f501,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',t1_subset)).

fof(f502,plain,
    ( ~ spl7_65
    | ~ spl7_8
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f448,f426,f208,f500])).

fof(f426,plain,
    ( spl7_54
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f448,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_8
    | ~ spl7_54 ),
    inference(unit_resulting_resolution,[],[f209,f427,f170])).

fof(f427,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f426])).

fof(f491,plain,
    ( ~ spl7_63
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f478,f465,f489])).

fof(f489,plain,
    ( spl7_63
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f478,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2)
    | ~ spl7_58 ),
    inference(unit_resulting_resolution,[],[f466,f153])).

fof(f474,plain,
    ( ~ spl7_61
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f451,f426,f472])).

fof(f472,plain,
    ( spl7_61
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f451,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl7_54 ),
    inference(unit_resulting_resolution,[],[f427,f153])).

fof(f467,plain,
    ( spl7_58
    | ~ spl7_8
    | ~ spl7_18
    | spl7_53 ),
    inference(avatar_split_clause,[],[f433,f417,f243,f208,f465])).

fof(f433,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f244,f418,f359])).

fof(f443,plain,
    ( ~ spl7_57
    | ~ spl7_8
    | spl7_53 ),
    inference(avatar_split_clause,[],[f436,f417,f208,f441])).

fof(f436,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_8
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f209,f418,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',t8_boole)).

fof(f428,plain,
    ( spl7_52
    | spl7_54
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f400,f236,f208,f426,f420])).

fof(f400,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(resolution,[],[f359,f237])).

fof(f397,plain,
    ( spl7_50
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f390,f387,f395])).

fof(f387,plain,
    ( spl7_48
  <=> o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f390,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_48 ),
    inference(superposition,[],[f152,f388])).

fof(f388,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f387])).

fof(f389,plain,
    ( spl7_48
    | ~ spl7_8
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f374,f366,f208,f387])).

fof(f366,plain,
    ( spl7_46
  <=> v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f374,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_8
    | ~ spl7_46 ),
    inference(unit_resulting_resolution,[],[f367,f280])).

fof(f367,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f366])).

fof(f368,plain,
    ( spl7_46
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f361,f208,f366])).

fof(f361,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f152,f360,f155])).

fof(f360,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f209,f152,f170])).

fof(f356,plain,
    ( spl7_44
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f342,f201,f187,f180,f354])).

fof(f342,plain,
    ( v6_lattices(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f202,f181,f188,f145])).

fof(f145,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',cc1_lattices)).

fof(f349,plain,
    ( spl7_42
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f341,f201,f187,f180,f347])).

fof(f341,plain,
    ( v4_lattices(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f202,f181,f188,f144])).

fof(f144,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f336,plain,
    ( spl7_40
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f300,f259,f334])).

fof(f334,plain,
    ( spl7_40
  <=> v1_funct_1(u1_lattices(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f259,plain,
    ( spl7_22
  <=> l1_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f300,plain,
    ( v1_funct_1(u1_lattices(sK6))
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f260,f138])).

fof(f138,plain,(
    ! [X0] :
      ( v1_funct_1(u1_lattices(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',dt_u1_lattices)).

fof(f260,plain,
    ( l1_lattices(sK6)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f259])).

fof(f329,plain,
    ( spl7_38
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f290,f275,f327])).

fof(f327,plain,
    ( spl7_38
  <=> v1_funct_1(u2_lattices(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f275,plain,
    ( spl7_26
  <=> l2_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f290,plain,
    ( v1_funct_1(u2_lattices(sK6))
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f276,f135])).

fof(f135,plain,(
    ! [X0] :
      ( v1_funct_1(u2_lattices(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',dt_u2_lattices)).

fof(f276,plain,
    ( l2_lattices(sK6)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f275])).

fof(f321,plain,
    ( spl7_36
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f299,f252,f319])).

fof(f319,plain,
    ( spl7_36
  <=> v1_funct_1(u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f299,plain,
    ( v1_funct_1(u1_lattices(sK0))
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f253,f138])).

fof(f314,plain,
    ( spl7_34
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f289,f268,f312])).

fof(f312,plain,
    ( spl7_34
  <=> v1_funct_1(u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f289,plain,
    ( v1_funct_1(u2_lattices(sK0))
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f269,f135])).

fof(f307,plain,
    ( spl7_32
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f298,f215,f305])).

fof(f305,plain,
    ( spl7_32
  <=> v1_funct_1(u1_lattices(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f215,plain,
    ( spl7_10
  <=> l1_lattices(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f298,plain,
    ( v1_funct_1(u1_lattices(sK4))
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f216,f138])).

fof(f216,plain,
    ( l1_lattices(sK4)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f215])).

fof(f297,plain,
    ( spl7_30
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f288,f222,f295])).

fof(f295,plain,
    ( spl7_30
  <=> v1_funct_1(u2_lattices(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f222,plain,
    ( spl7_12
  <=> l2_lattices(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f288,plain,
    ( v1_funct_1(u2_lattices(sK5))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f223,f135])).

fof(f223,plain,
    ( l2_lattices(sK5)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f222])).

fof(f287,plain,
    ( spl7_28
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f278,f208,f285])).

fof(f285,plain,
    ( spl7_28
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f277,plain,
    ( spl7_26
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f263,f229,f275])).

fof(f229,plain,
    ( spl7_14
  <=> l3_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f263,plain,
    ( l2_lattices(sK6)
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f230,f142])).

fof(f142,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',dt_l3_lattices)).

fof(f230,plain,
    ( l3_lattices(sK6)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f229])).

fof(f270,plain,
    ( spl7_24
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f262,f201,f268])).

fof(f262,plain,
    ( l2_lattices(sK0)
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f202,f142])).

fof(f261,plain,
    ( spl7_22
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f247,f229,f259])).

fof(f247,plain,
    ( l1_lattices(sK6)
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f230,f141])).

fof(f141,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f254,plain,
    ( spl7_20
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f246,f201,f252])).

fof(f246,plain,
    ( l1_lattices(sK0)
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f202,f141])).

fof(f245,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f131,f243])).

fof(f131,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f117])).

fof(f238,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f130,f236])).

fof(f130,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f117])).

fof(f231,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f175,f229])).

fof(f175,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f125])).

fof(f125,plain,(
    l3_lattices(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f124])).

fof(f124,plain,
    ( ? [X0] : l3_lattices(X0)
   => l3_lattices(sK6) ),
    introduced(choice_axiom,[])).

fof(f34,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',existence_l3_lattices)).

fof(f224,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f174,f222])).

fof(f174,plain,(
    l2_lattices(sK5) ),
    inference(cnf_transformation,[],[f123])).

fof(f123,plain,(
    l2_lattices(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f122])).

fof(f122,plain,
    ( ? [X0] : l2_lattices(X0)
   => l2_lattices(sK5) ),
    introduced(choice_axiom,[])).

fof(f33,axiom,(
    ? [X0] : l2_lattices(X0) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',existence_l2_lattices)).

fof(f217,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f173,f215])).

fof(f173,plain,(
    l1_lattices(sK4) ),
    inference(cnf_transformation,[],[f121])).

fof(f121,plain,(
    l1_lattices(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f120])).

fof(f120,plain,
    ( ? [X0] : l1_lattices(X0)
   => l1_lattices(sK4) ),
    introduced(choice_axiom,[])).

fof(f31,axiom,(
    ? [X0] : l1_lattices(X0) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',existence_l1_lattices)).

fof(f210,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f133,f208])).

fof(f133,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t52_filter_1.p',dt_o_0_0_xboole_0)).

fof(f203,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f129,f201])).

fof(f129,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f117])).

fof(f196,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f128,f194])).

fof(f128,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f117])).

fof(f189,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f127,f187])).

fof(f127,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f117])).

fof(f182,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f126,f180])).

fof(f126,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f117])).
%------------------------------------------------------------------------------
