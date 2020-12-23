%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t22_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:12 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  375 ( 987 expanded)
%              Number of leaves         :   97 ( 421 expanded)
%              Depth                    :    9
%              Number of atoms          : 1002 (3047 expanded)
%              Number of equality atoms :   26 (  80 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f823,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f136,f143,f150,f157,f164,f171,f178,f185,f192,f199,f206,f215,f222,f232,f241,f255,f264,f271,f282,f289,f301,f309,f318,f325,f339,f348,f356,f363,f372,f379,f386,f396,f405,f414,f423,f444,f451,f458,f476,f493,f500,f510,f519,f532,f556,f567,f577,f594,f612,f621,f633,f635,f637,f639,f641,f645,f646,f654,f661,f668,f689,f705,f715,f722,f740,f742,f743,f753,f774,f781,f794,f815,f817,f819,f821])).

fof(f821,plain,
    ( spl7_103
    | ~ spl7_118
    | ~ spl7_124 ),
    inference(avatar_contradiction_clause,[],[f820])).

fof(f820,plain,
    ( $false
    | ~ spl7_103
    | ~ spl7_118
    | ~ spl7_124 ),
    inference(subsumption_resolution,[],[f805,f326])).

fof(f326,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[],[f108,f96])).

fof(f96,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',t2_boole)).

fof(f108,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',commutativity_k3_xboole_0)).

fof(f805,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | ~ spl7_103
    | ~ spl7_118
    | ~ spl7_124 ),
    inference(backward_demodulation,[],[f799,f674])).

fof(f674,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK1)) != k1_xboole_0
    | ~ spl7_103 ),
    inference(unit_resulting_resolution,[],[f653,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',d7_xboole_0)).

fof(f653,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl7_103 ),
    inference(avatar_component_clause,[],[f652])).

fof(f652,plain,
    ( spl7_103
  <=> ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f799,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | ~ spl7_118
    | ~ spl7_124 ),
    inference(forward_demodulation,[],[f796,f763])).

fof(f763,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = k1_xboole_0
    | ~ spl7_118 ),
    inference(unit_resulting_resolution,[],[f752,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f752,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl7_118 ),
    inference(avatar_component_clause,[],[f751])).

fof(f751,plain,
    ( spl7_118
  <=> r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).

fof(f796,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(sK1)
    | ~ spl7_124 ),
    inference(unit_resulting_resolution,[],[f793,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',t28_xboole_1)).

fof(f793,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl7_124 ),
    inference(avatar_component_clause,[],[f792])).

fof(f792,plain,
    ( spl7_124
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f819,plain,
    ( spl7_103
    | ~ spl7_118
    | ~ spl7_124 ),
    inference(avatar_contradiction_clause,[],[f818])).

fof(f818,plain,
    ( $false
    | ~ spl7_103
    | ~ spl7_118
    | ~ spl7_124 ),
    inference(subsumption_resolution,[],[f804,f479])).

fof(f479,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f326,f120])).

fof(f804,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_103
    | ~ spl7_118
    | ~ spl7_124 ),
    inference(backward_demodulation,[],[f799,f653])).

fof(f817,plain,
    ( ~ spl7_26
    | spl7_53
    | ~ spl7_118
    | ~ spl7_124 ),
    inference(avatar_contradiction_clause,[],[f816])).

fof(f816,plain,
    ( $false
    | ~ spl7_26
    | ~ spl7_53
    | ~ spl7_118
    | ~ spl7_124 ),
    inference(subsumption_resolution,[],[f801,f242])).

fof(f242,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f231,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',t7_boole)).

fof(f231,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl7_26
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f801,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_xboole_0)
    | ~ spl7_53
    | ~ spl7_118
    | ~ spl7_124 ),
    inference(backward_demodulation,[],[f799,f429])).

fof(f429,plain,
    ( r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f347,f106,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',t2_subset)).

fof(f106,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',existence_m1_subset_1)).

fof(f347,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl7_53
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f815,plain,
    ( ~ spl7_26
    | spl7_53
    | ~ spl7_118
    | ~ spl7_124 ),
    inference(avatar_contradiction_clause,[],[f814])).

fof(f814,plain,
    ( $false
    | ~ spl7_26
    | ~ spl7_53
    | ~ spl7_118
    | ~ spl7_124 ),
    inference(subsumption_resolution,[],[f800,f231])).

fof(f800,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_53
    | ~ spl7_118
    | ~ spl7_124 ),
    inference(backward_demodulation,[],[f799,f347])).

fof(f794,plain,
    ( spl7_124
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f786,f204,f197,f190,f148,f141,f792])).

fof(f141,plain,
    ( spl7_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f148,plain,
    ( spl7_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f190,plain,
    ( spl7_16
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f197,plain,
    ( spl7_18
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f204,plain,
    ( spl7_20
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f786,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f142,f149,f191,f198,f205,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',t4_tsep_1)).

fof(f205,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f204])).

fof(f198,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f197])).

fof(f191,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f190])).

fof(f149,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f148])).

fof(f142,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f141])).

fof(f781,plain,
    ( spl7_122
    | spl7_53
    | spl7_55
    | ~ spl7_118 ),
    inference(avatar_split_clause,[],[f762,f751,f354,f346,f779])).

fof(f779,plain,
    ( spl7_122
  <=> r2_subset_1(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).

fof(f354,plain,
    ( spl7_55
  <=> ~ v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f762,plain,
    ( r2_subset_1(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl7_53
    | ~ spl7_55
    | ~ spl7_118 ),
    inference(unit_resulting_resolution,[],[f347,f355,f752,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r2_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( ( r2_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r2_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',redefinition_r2_subset_1)).

fof(f355,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f354])).

fof(f774,plain,
    ( spl7_120
    | spl7_53
    | spl7_55
    | ~ spl7_116 ),
    inference(avatar_split_clause,[],[f755,f738,f354,f346,f772])).

fof(f772,plain,
    ( spl7_120
  <=> r2_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f738,plain,
    ( spl7_116
  <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).

fof(f755,plain,
    ( r2_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl7_53
    | ~ spl7_55
    | ~ spl7_116 ),
    inference(unit_resulting_resolution,[],[f355,f347,f739,f117])).

fof(f739,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl7_116 ),
    inference(avatar_component_clause,[],[f738])).

fof(f753,plain,
    ( spl7_118
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f691,f307,f299,f247,f751])).

fof(f247,plain,
    ( spl7_30
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f299,plain,
    ( spl7_42
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f307,plain,
    ( spl7_44
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f691,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f300,f308,f248,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',d3_tsep_1)).

fof(f248,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f247])).

fof(f308,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f307])).

fof(f300,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f299])).

fof(f743,plain,
    ( spl7_32
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f647,f307,f299,f247,f253])).

fof(f253,plain,
    ( spl7_32
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f647,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f300,f308,f248,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',symmetry_r1_tsep_1)).

fof(f742,plain,
    ( ~ spl7_30
    | spl7_33
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f741])).

fof(f741,plain,
    ( $false
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f251,f647])).

fof(f251,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl7_33
  <=> ~ r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f740,plain,
    ( spl7_116
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f690,f307,f299,f253,f738])).

fof(f690,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f308,f300,f254,f97])).

fof(f254,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f253])).

fof(f722,plain,
    ( ~ spl7_115
    | ~ spl7_44
    | spl7_105 ),
    inference(avatar_split_clause,[],[f694,f659,f307,f720])).

fof(f720,plain,
    ( spl7_115
  <=> ~ r1_tsep_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).

fof(f659,plain,
    ( spl7_105
  <=> ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).

fof(f694,plain,
    ( ~ r1_tsep_1(sK2,sK2)
    | ~ spl7_44
    | ~ spl7_105 ),
    inference(unit_resulting_resolution,[],[f308,f308,f660,f97])).

fof(f660,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ spl7_105 ),
    inference(avatar_component_clause,[],[f659])).

fof(f715,plain,
    ( ~ spl7_113
    | ~ spl7_42
    | spl7_103 ),
    inference(avatar_split_clause,[],[f693,f652,f299,f713])).

fof(f713,plain,
    ( spl7_113
  <=> ~ r1_tsep_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).

fof(f693,plain,
    ( ~ r1_tsep_1(sK1,sK1)
    | ~ spl7_42
    | ~ spl7_103 ),
    inference(unit_resulting_resolution,[],[f300,f300,f653,f97])).

fof(f705,plain,
    ( ~ spl7_111
    | ~ spl7_22
    | spl7_101 ),
    inference(avatar_split_clause,[],[f692,f619,f213,f703])).

fof(f703,plain,
    ( spl7_111
  <=> ~ r1_tsep_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_111])])).

fof(f213,plain,
    ( spl7_22
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f619,plain,
    ( spl7_101
  <=> ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).

fof(f692,plain,
    ( ~ r1_tsep_1(sK0,sK0)
    | ~ spl7_22
    | ~ spl7_101 ),
    inference(unit_resulting_resolution,[],[f214,f214,f620,f97])).

fof(f620,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl7_101 ),
    inference(avatar_component_clause,[],[f619])).

fof(f214,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f213])).

fof(f689,plain,
    ( spl7_108
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f340,f337,f687])).

fof(f687,plain,
    ( spl7_108
  <=> m1_pre_topc(sK3(sK3(sK6)),sK3(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f337,plain,
    ( spl7_50
  <=> l1_pre_topc(sK3(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f340,plain,
    ( m1_pre_topc(sK3(sK3(sK6)),sK3(sK6))
    | ~ spl7_50 ),
    inference(unit_resulting_resolution,[],[f338,f101])).

fof(f101,plain,(
    ! [X0] :
      ( m1_pre_topc(sK3(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( m1_pre_topc(sK3(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
     => m1_pre_topc(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',existence_m1_pre_topc)).

fof(f338,plain,
    ( l1_pre_topc(sK3(sK6))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f337])).

fof(f668,plain,
    ( ~ spl7_107
    | spl7_97 ),
    inference(avatar_split_clause,[],[f603,f592,f666])).

fof(f666,plain,
    ( spl7_107
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).

fof(f592,plain,
    ( spl7_97
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f603,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_97 ),
    inference(unit_resulting_resolution,[],[f593,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',t1_subset)).

fof(f593,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_97 ),
    inference(avatar_component_clause,[],[f592])).

fof(f661,plain,
    ( ~ spl7_105
    | spl7_55
    | spl7_77 ),
    inference(avatar_split_clause,[],[f597,f456,f354,f659])).

fof(f456,plain,
    ( spl7_77
  <=> ~ r2_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f597,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ spl7_55
    | ~ spl7_77 ),
    inference(unit_resulting_resolution,[],[f355,f355,f457,f117])).

fof(f457,plain,
    ( ~ r2_subset_1(u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ spl7_77 ),
    inference(avatar_component_clause,[],[f456])).

fof(f654,plain,
    ( ~ spl7_103
    | spl7_53
    | spl7_75 ),
    inference(avatar_split_clause,[],[f596,f449,f346,f652])).

fof(f449,plain,
    ( spl7_75
  <=> ~ r2_subset_1(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f596,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl7_53
    | ~ spl7_75 ),
    inference(unit_resulting_resolution,[],[f347,f347,f450,f117])).

fof(f450,plain,
    ( ~ r2_subset_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f449])).

fof(f646,plain,
    ( spl7_30
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f627,f307,f299,f253,f247])).

fof(f627,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f308,f300,f254,f118])).

fof(f645,plain,
    ( spl7_31
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f644])).

fof(f644,plain,
    ( $false
    | ~ spl7_31
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f643,f308])).

fof(f643,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl7_31
    | ~ spl7_32
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f642,f300])).

fof(f642,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ spl7_31
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f632,f254])).

fof(f632,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ spl7_31 ),
    inference(resolution,[],[f118,f245])).

fof(f245,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl7_31
  <=> ~ r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f641,plain,
    ( spl7_31
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f640])).

fof(f640,plain,
    ( $false
    | ~ spl7_31
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f627,f245])).

fof(f639,plain,
    ( spl7_31
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f638])).

fof(f638,plain,
    ( $false
    | ~ spl7_31
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f628,f254])).

fof(f628,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ spl7_31
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f308,f300,f245,f118])).

fof(f637,plain,
    ( spl7_31
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f636])).

fof(f636,plain,
    ( $false
    | ~ spl7_31
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f629,f300])).

fof(f629,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl7_31
    | ~ spl7_32
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f308,f254,f245,f118])).

fof(f635,plain,
    ( spl7_31
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f634])).

fof(f634,plain,
    ( $false
    | ~ spl7_31
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f630,f308])).

fof(f630,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl7_31
    | ~ spl7_32
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f300,f254,f245,f118])).

fof(f633,plain,
    ( spl7_31
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f631])).

fof(f631,plain,
    ( $false
    | ~ spl7_31
    | ~ spl7_32
    | ~ spl7_42
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f308,f300,f254,f245,f118])).

fof(f621,plain,
    ( ~ spl7_101
    | spl7_49
    | spl7_73 ),
    inference(avatar_split_clause,[],[f595,f442,f323,f619])).

fof(f323,plain,
    ( spl7_49
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f442,plain,
    ( spl7_73
  <=> ~ r2_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f595,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl7_49
    | ~ spl7_73 ),
    inference(unit_resulting_resolution,[],[f324,f324,f443,f117])).

fof(f443,plain,
    ( ~ r2_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl7_73 ),
    inference(avatar_component_clause,[],[f442])).

fof(f324,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f323])).

fof(f612,plain,
    ( ~ spl7_99
    | spl7_97 ),
    inference(avatar_split_clause,[],[f602,f592,f610])).

fof(f610,plain,
    ( spl7_99
  <=> ~ r1_tarski(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).

fof(f602,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl7_97 ),
    inference(unit_resulting_resolution,[],[f593,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',t3_subset)).

fof(f594,plain,
    ( ~ spl7_97
    | ~ spl7_26
    | ~ spl7_80 ),
    inference(avatar_split_clause,[],[f581,f491,f230,f592])).

fof(f491,plain,
    ( spl7_80
  <=> r2_hidden(sK4(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f581,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_26
    | ~ spl7_80 ),
    inference(unit_resulting_resolution,[],[f231,f492,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',t5_subset)).

fof(f492,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_80 ),
    inference(avatar_component_clause,[],[f491])).

fof(f577,plain,
    ( spl7_94
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f560,f554,f575])).

fof(f575,plain,
    ( spl7_94
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f554,plain,
    ( spl7_90
  <=> k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f560,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_90 ),
    inference(superposition,[],[f106,f555])).

fof(f555,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_90 ),
    inference(avatar_component_clause,[],[f554])).

fof(f567,plain,
    ( spl7_92
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f557,f554,f565])).

fof(f565,plain,
    ( spl7_92
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f557,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_90 ),
    inference(superposition,[],[f349,f555])).

fof(f349,plain,(
    ! [X0] : r1_tarski(sK4(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f106,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f556,plain,
    ( spl7_90
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f539,f530,f554])).

fof(f530,plain,
    ( spl7_88
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f539,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f531,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',t6_boole)).

fof(f531,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f530])).

fof(f532,plain,
    ( spl7_88
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f521,f230,f530])).

fof(f521,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f502,f432])).

fof(f432,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f113,f106])).

fof(f502,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f231,f106,f126])).

fof(f519,plain,
    ( spl7_86
    | ~ spl7_84 ),
    inference(avatar_split_clause,[],[f512,f508,f517])).

fof(f517,plain,
    ( spl7_86
  <=> l1_struct_0(sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f508,plain,
    ( spl7_84
  <=> l1_pre_topc(sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f512,plain,
    ( l1_struct_0(sK3(sK3(sK0)))
    | ~ spl7_84 ),
    inference(unit_resulting_resolution,[],[f509,f99])).

fof(f99,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',dt_l1_pre_topc)).

fof(f509,plain,
    ( l1_pre_topc(sK3(sK3(sK0)))
    | ~ spl7_84 ),
    inference(avatar_component_clause,[],[f508])).

fof(f510,plain,
    ( spl7_84
    | ~ spl7_46
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f501,f474,f316,f508])).

fof(f316,plain,
    ( spl7_46
  <=> l1_pre_topc(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f474,plain,
    ( spl7_78
  <=> m1_pre_topc(sK3(sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f501,plain,
    ( l1_pre_topc(sK3(sK3(sK0)))
    | ~ spl7_46
    | ~ spl7_78 ),
    inference(unit_resulting_resolution,[],[f317,f475,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',dt_m1_pre_topc)).

fof(f475,plain,
    ( m1_pre_topc(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f474])).

fof(f317,plain,
    ( l1_pre_topc(sK3(sK0))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f316])).

fof(f500,plain,
    ( ~ spl7_83
    | spl7_49 ),
    inference(avatar_split_clause,[],[f467,f323,f498])).

fof(f498,plain,
    ( spl7_83
  <=> ~ r2_hidden(u1_struct_0(sK0),sK4(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f467,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK4(u1_struct_0(sK0)))
    | ~ spl7_49 ),
    inference(unit_resulting_resolution,[],[f324,f464])).

fof(f464,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f432,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',antisymmetry_r2_hidden)).

fof(f493,plain,
    ( spl7_80
    | spl7_49 ),
    inference(avatar_split_clause,[],[f428,f323,f491])).

fof(f428,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_49 ),
    inference(unit_resulting_resolution,[],[f324,f106,f113])).

fof(f476,plain,
    ( spl7_78
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f330,f316,f474])).

fof(f330,plain,
    ( m1_pre_topc(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl7_46 ),
    inference(unit_resulting_resolution,[],[f317,f101])).

fof(f458,plain,
    ( ~ spl7_77
    | spl7_55 ),
    inference(avatar_split_clause,[],[f365,f354,f456])).

fof(f365,plain,
    ( ~ r2_subset_1(u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ spl7_55 ),
    inference(unit_resulting_resolution,[],[f355,f129])).

fof(f129,plain,(
    ! [X0] :
      ( ~ r2_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(condensation,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r2_subset_1(X0,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_subset_1(X0,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_subset_1(X0,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ r2_subset_1(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',irreflexivity_r2_subset_1)).

fof(f451,plain,
    ( ~ spl7_75
    | spl7_53 ),
    inference(avatar_split_clause,[],[f364,f346,f449])).

fof(f364,plain,
    ( ~ r2_subset_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f347,f129])).

fof(f444,plain,
    ( ~ spl7_73
    | spl7_49 ),
    inference(avatar_split_clause,[],[f332,f323,f442])).

fof(f332,plain,
    ( ~ r2_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl7_49 ),
    inference(unit_resulting_resolution,[],[f324,f129])).

fof(f423,plain,
    ( spl7_70
    | ~ spl7_68 ),
    inference(avatar_split_clause,[],[f416,f412,f421])).

fof(f421,plain,
    ( spl7_70
  <=> l1_struct_0(sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f412,plain,
    ( spl7_68
  <=> l1_pre_topc(sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f416,plain,
    ( l1_struct_0(sK3(sK2))
    | ~ spl7_68 ),
    inference(unit_resulting_resolution,[],[f413,f99])).

fof(f413,plain,
    ( l1_pre_topc(sK3(sK2))
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f412])).

fof(f414,plain,
    ( spl7_68
    | ~ spl7_40
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f406,f384,f287,f412])).

fof(f287,plain,
    ( spl7_40
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f384,plain,
    ( spl7_62
  <=> m1_pre_topc(sK3(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f406,plain,
    ( l1_pre_topc(sK3(sK2))
    | ~ spl7_40
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f288,f385,f100])).

fof(f385,plain,
    ( m1_pre_topc(sK3(sK2),sK2)
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f384])).

fof(f288,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f287])).

fof(f405,plain,
    ( spl7_66
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f398,f394,f403])).

fof(f403,plain,
    ( spl7_66
  <=> l1_struct_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f394,plain,
    ( spl7_64
  <=> l1_pre_topc(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f398,plain,
    ( l1_struct_0(sK3(sK1))
    | ~ spl7_64 ),
    inference(unit_resulting_resolution,[],[f395,f99])).

fof(f395,plain,
    ( l1_pre_topc(sK3(sK1))
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f394])).

fof(f396,plain,
    ( spl7_64
    | ~ spl7_38
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f387,f377,f280,f394])).

fof(f280,plain,
    ( spl7_38
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f377,plain,
    ( spl7_60
  <=> m1_pre_topc(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f387,plain,
    ( l1_pre_topc(sK3(sK1))
    | ~ spl7_38
    | ~ spl7_60 ),
    inference(unit_resulting_resolution,[],[f281,f378,f100])).

fof(f378,plain,
    ( m1_pre_topc(sK3(sK1),sK1)
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f377])).

fof(f281,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f280])).

fof(f386,plain,
    ( spl7_62
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f293,f287,f384])).

fof(f293,plain,
    ( m1_pre_topc(sK3(sK2),sK2)
    | ~ spl7_40 ),
    inference(unit_resulting_resolution,[],[f288,f101])).

fof(f379,plain,
    ( spl7_60
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f290,f280,f377])).

fof(f290,plain,
    ( m1_pre_topc(sK3(sK1),sK1)
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f281,f101])).

fof(f372,plain,
    ( spl7_58
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f341,f337,f370])).

fof(f370,plain,
    ( spl7_58
  <=> l1_struct_0(sK3(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f341,plain,
    ( l1_struct_0(sK3(sK6))
    | ~ spl7_50 ),
    inference(unit_resulting_resolution,[],[f338,f99])).

fof(f363,plain,
    ( spl7_56
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f331,f316,f361])).

fof(f361,plain,
    ( spl7_56
  <=> l1_struct_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f331,plain,
    ( l1_struct_0(sK3(sK0))
    | ~ spl7_46 ),
    inference(unit_resulting_resolution,[],[f317,f99])).

fof(f356,plain,
    ( ~ spl7_55
    | spl7_9
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f311,f307,f162,f354])).

fof(f162,plain,
    ( spl7_9
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f311,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl7_9
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f163,f308,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',fc2_struct_0)).

fof(f163,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f162])).

fof(f348,plain,
    ( ~ spl7_53
    | spl7_7
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f310,f299,f155,f346])).

fof(f155,plain,
    ( spl7_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f310,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_7
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f156,f300,f103])).

fof(f156,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f155])).

fof(f339,plain,
    ( spl7_50
    | ~ spl7_14
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f275,f269,f183,f337])).

fof(f183,plain,
    ( spl7_14
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f269,plain,
    ( spl7_36
  <=> m1_pre_topc(sK3(sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f275,plain,
    ( l1_pre_topc(sK3(sK6))
    | ~ spl7_14
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f184,f270,f100])).

fof(f270,plain,
    ( m1_pre_topc(sK3(sK6),sK6)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f269])).

fof(f184,plain,
    ( l1_pre_topc(sK6)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f183])).

fof(f325,plain,
    ( ~ spl7_49
    | spl7_1
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f302,f213,f134,f323])).

fof(f134,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f302,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f135,f214,f103])).

fof(f135,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f318,plain,
    ( spl7_46
    | ~ spl7_4
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f274,f262,f148,f316])).

fof(f262,plain,
    ( spl7_34
  <=> m1_pre_topc(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f274,plain,
    ( l1_pre_topc(sK3(sK0))
    | ~ spl7_4
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f149,f263,f100])).

fof(f263,plain,
    ( m1_pre_topc(sK3(sK0),sK0)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f262])).

fof(f309,plain,
    ( spl7_44
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f294,f287,f307])).

fof(f294,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_40 ),
    inference(unit_resulting_resolution,[],[f288,f99])).

fof(f301,plain,
    ( spl7_42
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f291,f280,f299])).

fof(f291,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f281,f99])).

fof(f289,plain,
    ( spl7_40
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f273,f197,f148,f287])).

fof(f273,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f149,f198,f100])).

fof(f282,plain,
    ( spl7_38
    | ~ spl7_4
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f272,f190,f148,f280])).

fof(f272,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_4
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f149,f191,f100])).

fof(f271,plain,
    ( spl7_36
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f257,f183,f269])).

fof(f257,plain,
    ( m1_pre_topc(sK3(sK6),sK6)
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f184,f101])).

fof(f264,plain,
    ( spl7_34
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f256,f148,f262])).

fof(f256,plain,
    ( m1_pre_topc(sK3(sK0),sK0)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f149,f101])).

fof(f255,plain,
    ( spl7_30
    | spl7_32 ),
    inference(avatar_split_clause,[],[f94,f253,f247])).

fof(f94,plain,
    ( r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,
    ( ( r1_tsep_1(sK2,sK1)
      | r1_tsep_1(sK1,sK2) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f71,f70,f69])).

fof(f69,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( r1_tsep_1(X2,X1)
                  | r1_tsep_1(X1,X2) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( r1_tsep_1(X2,sK1)
              | r1_tsep_1(sK1,X2) )
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( r1_tsep_1(X2,X1)
            | r1_tsep_1(X1,X2) )
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( r1_tsep_1(sK2,X1)
          | r1_tsep_1(X1,sK2) )
        & m1_pre_topc(X1,sK2)
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',t22_tmap_1)).

fof(f241,plain,
    ( spl7_28
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f223,f169,f239])).

fof(f239,plain,
    ( spl7_28
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f169,plain,
    ( spl7_10
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f223,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f170,f102])).

fof(f170,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f169])).

fof(f232,plain,
    ( spl7_26
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f225,f169,f230])).

fof(f225,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f223,f170])).

fof(f222,plain,
    ( spl7_24
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f208,f183,f220])).

fof(f220,plain,
    ( spl7_24
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f208,plain,
    ( l1_struct_0(sK6)
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f184,f99])).

fof(f215,plain,
    ( spl7_22
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f207,f148,f213])).

fof(f207,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f149,f99])).

fof(f206,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f93,f204])).

fof(f93,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f199,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f92,f197])).

fof(f92,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f192,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f90,f190])).

fof(f90,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f185,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f128,f183])).

fof(f128,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f84])).

fof(f84,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK6) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',existence_l1_pre_topc)).

fof(f178,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f127,f176])).

fof(f176,plain,
    ( spl7_12
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f127,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    l1_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f82])).

fof(f82,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK5) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',existence_l1_struct_0)).

fof(f171,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f95,f169])).

fof(f95,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t22_tmap_1.p',dt_o_0_0_xboole_0)).

fof(f164,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f91,f162])).

fof(f91,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f157,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f89,f155])).

fof(f89,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f150,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f88,f148])).

fof(f88,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f143,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f87,f141])).

fof(f87,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f136,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f86,f134])).

fof(f86,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f72])).
%------------------------------------------------------------------------------
