%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t40_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:14 EDT 2019

% Result     : Theorem 2.44s
% Output     : Refutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  369 ( 841 expanded)
%              Number of leaves         :   81 ( 361 expanded)
%              Depth                    :   14
%              Number of atoms          : 1403 (4699 expanded)
%              Number of equality atoms :  121 ( 245 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34332,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f227,f241,f248,f255,f269,f290,f297,f304,f320,f337,f357,f364,f372,f535,f662,f667,f672,f787,f937,f1003,f1143,f1306,f1311,f1825,f1867,f1913,f1968,f1973,f2961,f3489,f3706,f4713,f4723,f4750,f4760,f4781,f4786,f4812,f4824,f5020,f5027,f5034,f5873,f6675,f7129,f24270,f24420,f27646,f28011,f28108,f28145,f30313,f30342,f31266,f34205,f34331])).

fof(f34331,plain,
    ( spl11_424
    | ~ spl11_26
    | ~ spl11_250
    | ~ spl11_1120 ),
    inference(avatar_split_clause,[],[f34327,f32438,f2959,f318,f5585])).

fof(f5585,plain,
    ( spl11_424
  <=> v1_xboole_0(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_424])])).

fof(f318,plain,
    ( spl11_26
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f2959,plain,
    ( spl11_250
  <=> k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_250])])).

fof(f32438,plain,
    ( spl11_1120
  <=> ! [X0] :
        ( ~ v1_xboole_0(k3_xboole_0(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
        | v1_xboole_0(k3_xboole_0(X0,u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1120])])).

fof(f34327,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl11_26
    | ~ spl11_250
    | ~ spl11_1120 ),
    inference(forward_demodulation,[],[f34326,f179])).

fof(f179,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',commutativity_k3_xboole_0)).

fof(f34326,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)))
    | ~ spl11_26
    | ~ spl11_250
    | ~ spl11_1120 ),
    inference(subsumption_resolution,[],[f34323,f319])).

fof(f319,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f318])).

fof(f34323,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)))
    | ~ spl11_250
    | ~ spl11_1120 ),
    inference(superposition,[],[f32439,f2960])).

fof(f2960,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = k1_xboole_0
    | ~ spl11_250 ),
    inference(avatar_component_clause,[],[f2959])).

fof(f32439,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k3_xboole_0(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
        | v1_xboole_0(k3_xboole_0(X0,u1_struct_0(sK2))) )
    | ~ spl11_1120 ),
    inference(avatar_component_clause,[],[f32438])).

fof(f34205,plain,
    ( spl11_1120
    | ~ spl11_286 ),
    inference(avatar_split_clause,[],[f26415,f3487,f32438])).

fof(f3487,plain,
    ( spl11_286
  <=> u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_286])])).

fof(f26415,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k3_xboole_0(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
        | v1_xboole_0(k3_xboole_0(X0,u1_struct_0(sK2))) )
    | ~ spl11_286 ),
    inference(superposition,[],[f458,f3488])).

fof(f3488,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl11_286 ),
    inference(avatar_component_clause,[],[f3487])).

fof(f458,plain,(
    ! [X10,X8,X9] :
      ( ~ v1_xboole_0(k3_xboole_0(X8,k2_xboole_0(X9,X10)))
      | v1_xboole_0(k3_xboole_0(X8,X10)) ) ),
    inference(superposition,[],[f181,f197])).

fof(f197,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',t23_xboole_1)).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',fc5_xboole_0)).

fof(f31266,plain,
    ( ~ spl11_250
    | ~ spl11_322
    | spl11_403
    | ~ spl11_934 ),
    inference(avatar_contradiction_clause,[],[f31265])).

fof(f31265,plain,
    ( $false
    | ~ spl11_250
    | ~ spl11_322
    | ~ spl11_403
    | ~ spl11_934 ),
    inference(subsumption_resolution,[],[f31264,f5023])).

fof(f5023,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) != k1_xboole_0
    | ~ spl11_403 ),
    inference(avatar_component_clause,[],[f5022])).

fof(f5022,plain,
    ( spl11_403
  <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_403])])).

fof(f31264,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl11_250
    | ~ spl11_322
    | ~ spl11_934 ),
    inference(forward_demodulation,[],[f31171,f2960])).

fof(f31171,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl11_322
    | ~ spl11_934 ),
    inference(superposition,[],[f23917,f3705])).

fof(f3705,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_322 ),
    inference(avatar_component_clause,[],[f3704])).

fof(f3704,plain,
    ( spl11_322
  <=> u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_322])])).

fof(f23917,plain,
    ( ! [X5] : k3_xboole_0(X5,u1_struct_0(sK3)) = k3_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),X5))
    | ~ spl11_934 ),
    inference(avatar_component_clause,[],[f23916])).

fof(f23916,plain,
    ( spl11_934
  <=> ! [X5] : k3_xboole_0(X5,u1_struct_0(sK3)) = k3_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_934])])).

fof(f30342,plain,
    ( ~ spl11_424
    | spl11_437 ),
    inference(avatar_contradiction_clause,[],[f30339])).

fof(f30339,plain,
    ( $false
    | ~ spl11_424
    | ~ spl11_437 ),
    inference(unit_resulting_resolution,[],[f5586,f5869,f167])).

fof(f167,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',t6_boole)).

fof(f5869,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) != k1_xboole_0
    | ~ spl11_437 ),
    inference(avatar_component_clause,[],[f5868])).

fof(f5868,plain,
    ( spl11_437
  <=> k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_437])])).

fof(f5586,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl11_424 ),
    inference(avatar_component_clause,[],[f5585])).

fof(f30313,plain,
    ( ~ spl11_437
    | spl11_385 ),
    inference(avatar_split_clause,[],[f30295,f4807,f5868])).

fof(f4807,plain,
    ( spl11_385
  <=> ~ r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_385])])).

fof(f30295,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) != k1_xboole_0
    | ~ spl11_385 ),
    inference(resolution,[],[f4808,f378])).

fof(f378,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | k3_xboole_0(X2,X3) != k1_xboole_0 ) ),
    inference(resolution,[],[f192,f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',symmetry_r1_xboole_0)).

fof(f192,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',d7_xboole_0)).

fof(f4808,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl11_385 ),
    inference(avatar_component_clause,[],[f4807])).

fof(f28145,plain,
    ( spl11_55
    | ~ spl11_74
    | ~ spl11_76
    | ~ spl11_402 ),
    inference(avatar_contradiction_clause,[],[f28141])).

fof(f28141,plain,
    ( $false
    | ~ spl11_55
    | ~ spl11_74
    | ~ spl11_76
    | ~ spl11_402 ),
    inference(unit_resulting_resolution,[],[f658,f652,f5026,f519,f418])).

fof(f418,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != k1_xboole_0
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(resolution,[],[f166,f192])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',d3_tsep_1)).

fof(f519,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ spl11_55 ),
    inference(avatar_component_clause,[],[f518])).

fof(f518,plain,
    ( spl11_55
  <=> ~ r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_55])])).

fof(f5026,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl11_402 ),
    inference(avatar_component_clause,[],[f5025])).

fof(f5025,plain,
    ( spl11_402
  <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_402])])).

fof(f652,plain,
    ( l1_struct_0(sK1)
    | ~ spl11_74 ),
    inference(avatar_component_clause,[],[f651])).

fof(f651,plain,
    ( spl11_74
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_74])])).

fof(f658,plain,
    ( l1_struct_0(sK3)
    | ~ spl11_76 ),
    inference(avatar_component_clause,[],[f657])).

fof(f657,plain,
    ( spl11_76
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_76])])).

fof(f28108,plain,
    ( ~ spl11_52
    | ~ spl11_54
    | ~ spl11_56
    | ~ spl11_58
    | ~ spl11_60
    | ~ spl11_66 ),
    inference(avatar_contradiction_clause,[],[f28107])).

fof(f28107,plain,
    ( $false
    | ~ spl11_52
    | ~ spl11_54
    | ~ spl11_56
    | ~ spl11_58
    | ~ spl11_60
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f28106,f516])).

fof(f516,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl11_52
  <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f28106,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl11_54
    | ~ spl11_56
    | ~ spl11_58
    | ~ spl11_60
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f28095,f528])).

fof(f528,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_56 ),
    inference(avatar_component_clause,[],[f527])).

fof(f527,plain,
    ( spl11_56
  <=> r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f28095,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl11_54
    | ~ spl11_58
    | ~ spl11_60
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f28094,f522])).

fof(f522,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl11_54 ),
    inference(avatar_component_clause,[],[f521])).

fof(f521,plain,
    ( spl11_54
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_54])])).

fof(f28094,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ r1_tsep_1(sK1,sK3)
    | ~ spl11_58
    | ~ spl11_60
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f28093,f543])).

fof(f543,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl11_60 ),
    inference(avatar_component_clause,[],[f542])).

fof(f542,plain,
    ( spl11_60
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_60])])).

fof(f28093,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ r1_tsep_1(sK2,sK3)
    | ~ r1_tsep_1(sK1,sK3)
    | ~ spl11_58
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f28092,f534])).

fof(f534,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl11_58 ),
    inference(avatar_component_clause,[],[f533])).

fof(f533,plain,
    ( spl11_58
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f28092,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ r1_tsep_1(sK2,sK3)
    | ~ r1_tsep_1(sK1,sK3)
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f161,f591])).

fof(f591,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl11_66 ),
    inference(avatar_component_clause,[],[f590])).

fof(f590,plain,
    ( spl11_66
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).

fof(f161,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(sK3,sK2)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ r1_tsep_1(sK2,sK3)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,
    ( ( ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
        & r1_tsep_1(sK3,sK2)
        & r1_tsep_1(sK3,sK1) )
      | ( ( ~ r1_tsep_1(sK3,sK2)
          | ~ r1_tsep_1(sK3,sK1) )
        & r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) )
      | ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
        & r1_tsep_1(sK2,sK3)
        & r1_tsep_1(sK1,sK3) )
      | ( ( ~ r1_tsep_1(sK2,sK3)
          | ~ r1_tsep_1(sK1,sK3) )
        & r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ) )
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f57,f103,f102,f101,f100])).

fof(f100,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                        & r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) )
                      | ( ( ~ r1_tsep_1(X3,X2)
                          | ~ r1_tsep_1(X3,X1) )
                        & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                        & r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) )
                      | ( ( ~ r1_tsep_1(X2,X3)
                          | ~ r1_tsep_1(X1,X3) )
                        & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,sK1,X2))
                    & r1_tsep_1(X3,X2)
                    & r1_tsep_1(X3,sK1) )
                  | ( ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,sK1) )
                    & r1_tsep_1(X3,k1_tsep_1(X0,sK1,X2)) )
                  | ( ~ r1_tsep_1(k1_tsep_1(X0,sK1,X2),X3)
                    & r1_tsep_1(X2,X3)
                    & r1_tsep_1(sK1,X3) )
                  | ( ( ~ r1_tsep_1(X2,X3)
                      | ~ r1_tsep_1(sK1,X3) )
                    & r1_tsep_1(k1_tsep_1(X0,sK1,X2),X3) ) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                  & r1_tsep_1(X3,X2)
                  & r1_tsep_1(X3,X1) )
                | ( ( ~ r1_tsep_1(X3,X2)
                    | ~ r1_tsep_1(X3,X1) )
                  & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                  & r1_tsep_1(X2,X3)
                  & r1_tsep_1(X1,X3) )
                | ( ( ~ r1_tsep_1(X2,X3)
                    | ~ r1_tsep_1(X1,X3) )
                  & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,sK2))
                & r1_tsep_1(X3,sK2)
                & r1_tsep_1(X3,X1) )
              | ( ( ~ r1_tsep_1(X3,sK2)
                  | ~ r1_tsep_1(X3,X1) )
                & r1_tsep_1(X3,k1_tsep_1(X0,X1,sK2)) )
              | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,sK2),X3)
                & r1_tsep_1(sK2,X3)
                & r1_tsep_1(X1,X3) )
              | ( ( ~ r1_tsep_1(sK2,X3)
                  | ~ r1_tsep_1(X1,X3) )
                & r1_tsep_1(k1_tsep_1(X0,X1,sK2),X3) ) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
              & r1_tsep_1(X3,X2)
              & r1_tsep_1(X3,X1) )
            | ( ( ~ r1_tsep_1(X3,X2)
                | ~ r1_tsep_1(X3,X1) )
              & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
            | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
              & r1_tsep_1(X2,X3)
              & r1_tsep_1(X1,X3) )
            | ( ( ~ r1_tsep_1(X2,X3)
                | ~ r1_tsep_1(X1,X3) )
              & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( ( ~ r1_tsep_1(sK3,k1_tsep_1(X0,X1,X2))
            & r1_tsep_1(sK3,X2)
            & r1_tsep_1(sK3,X1) )
          | ( ( ~ r1_tsep_1(sK3,X2)
              | ~ r1_tsep_1(sK3,X1) )
            & r1_tsep_1(sK3,k1_tsep_1(X0,X1,X2)) )
          | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),sK3)
            & r1_tsep_1(X2,sK3)
            & r1_tsep_1(X1,sK3) )
          | ( ( ~ r1_tsep_1(X2,sK3)
              | ~ r1_tsep_1(X1,sK3) )
            & r1_tsep_1(k1_tsep_1(X0,X1,X2),sK3) ) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
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
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1) )
                       => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      & ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                       => ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1) ) )
                      & ( ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3) )
                       => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
                      & ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                       => ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) )
                     => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                     => ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) ) )
                    & ( ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) )
                     => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
                    & ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                     => ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',t40_tmap_1)).

fof(f28011,plain,
    ( spl11_251
    | ~ spl11_286
    | ~ spl11_436
    | ~ spl11_876 ),
    inference(avatar_contradiction_clause,[],[f28010])).

fof(f28010,plain,
    ( $false
    | ~ spl11_251
    | ~ spl11_286
    | ~ spl11_436
    | ~ spl11_876 ),
    inference(subsumption_resolution,[],[f28009,f2957])).

fof(f2957,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | ~ spl11_251 ),
    inference(avatar_component_clause,[],[f2956])).

fof(f2956,plain,
    ( spl11_251
  <=> k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_251])])).

fof(f28009,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = k1_xboole_0
    | ~ spl11_286
    | ~ spl11_436
    | ~ spl11_876 ),
    inference(forward_demodulation,[],[f28008,f5872])).

fof(f5872,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl11_436 ),
    inference(avatar_component_clause,[],[f5871])).

fof(f5871,plain,
    ( spl11_436
  <=> k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_436])])).

fof(f28008,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl11_286
    | ~ spl11_876 ),
    inference(forward_demodulation,[],[f27916,f179])).

fof(f27916,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl11_286
    | ~ spl11_876 ),
    inference(superposition,[],[f23397,f3488])).

fof(f23397,plain,
    ( ! [X0] : k3_xboole_0(u1_struct_0(sK3),X0) = k3_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),X0))
    | ~ spl11_876 ),
    inference(avatar_component_clause,[],[f23396])).

fof(f23396,plain,
    ( spl11_876
  <=> ! [X0] : k3_xboole_0(u1_struct_0(sK3),X0) = k3_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_876])])).

fof(f27646,plain,
    ( spl11_934
    | ~ spl11_404 ),
    inference(avatar_split_clause,[],[f18404,f5032,f23916])).

fof(f5032,plain,
    ( spl11_404
  <=> k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_404])])).

fof(f18404,plain,
    ( ! [X40] : k3_xboole_0(X40,u1_struct_0(sK3)) = k3_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),X40))
    | ~ spl11_404 ),
    inference(forward_demodulation,[],[f18314,f163])).

fof(f163,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',t1_boole)).

fof(f18314,plain,
    ( ! [X40] : k2_xboole_0(k3_xboole_0(X40,u1_struct_0(sK3)),k1_xboole_0) = k3_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),X40))
    | ~ spl11_404 ),
    inference(superposition,[],[f1020,f5033])).

fof(f5033,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) = k1_xboole_0
    | ~ spl11_404 ),
    inference(avatar_component_clause,[],[f5032])).

fof(f1020,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(X8,k2_xboole_0(X9,X10)) ),
    inference(superposition,[],[f449,f180])).

fof(f180,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',commutativity_k2_xboole_0)).

fof(f449,plain,(
    ! [X6,X4,X5] : k2_xboole_0(k3_xboole_0(X4,X6),k3_xboole_0(X5,X4)) = k3_xboole_0(X4,k2_xboole_0(X6,X5)) ),
    inference(superposition,[],[f197,f179])).

fof(f24420,plain,
    ( spl11_876
    | ~ spl11_402 ),
    inference(avatar_split_clause,[],[f15115,f5025,f23396])).

fof(f15115,plain,
    ( ! [X29] : k3_xboole_0(u1_struct_0(sK3),X29) = k3_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),X29))
    | ~ spl11_402 ),
    inference(forward_demodulation,[],[f15040,f163])).

fof(f15040,plain,
    ( ! [X29] : k2_xboole_0(k3_xboole_0(u1_struct_0(sK3),X29),k1_xboole_0) = k3_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),X29))
    | ~ spl11_402 ),
    inference(superposition,[],[f980,f5026])).

fof(f980,plain,(
    ! [X6,X8,X7] : k2_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k2_xboole_0(X6,X8)) ),
    inference(superposition,[],[f444,f180])).

fof(f444,plain,(
    ! [X6,X4,X5] : k2_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(X4,X6)) = k3_xboole_0(X4,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f197,f179])).

fof(f24270,plain,
    ( spl11_876
    | ~ spl11_400 ),
    inference(avatar_split_clause,[],[f14918,f5018,f23396])).

fof(f5018,plain,
    ( spl11_400
  <=> k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_400])])).

fof(f14918,plain,
    ( ! [X6] : k3_xboole_0(u1_struct_0(sK3),X6) = k3_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),X6))
    | ~ spl11_400 ),
    inference(forward_demodulation,[],[f14856,f163])).

fof(f14856,plain,
    ( ! [X6] : k2_xboole_0(k3_xboole_0(u1_struct_0(sK3),X6),k1_xboole_0) = k3_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),X6))
    | ~ spl11_400 ),
    inference(superposition,[],[f453,f5019])).

fof(f5019,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) = k1_xboole_0
    | ~ spl11_400 ),
    inference(avatar_component_clause,[],[f5018])).

fof(f453,plain,(
    ! [X6,X7,X5] : k2_xboole_0(k3_xboole_0(X5,X7),k3_xboole_0(X5,X6)) = k3_xboole_0(X5,k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f197,f180])).

fof(f7129,plain,
    ( spl11_67
    | ~ spl11_76
    | ~ spl11_382
    | ~ spl11_436 ),
    inference(avatar_contradiction_clause,[],[f7128])).

fof(f7128,plain,
    ( $false
    | ~ spl11_67
    | ~ spl11_76
    | ~ spl11_382
    | ~ spl11_436 ),
    inference(subsumption_resolution,[],[f7127,f658])).

fof(f7127,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl11_67
    | ~ spl11_382
    | ~ spl11_436 ),
    inference(subsumption_resolution,[],[f7126,f4777])).

fof(f4777,plain,
    ( l1_struct_0(sK2)
    | ~ spl11_382 ),
    inference(avatar_component_clause,[],[f4776])).

fof(f4776,plain,
    ( spl11_382
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_382])])).

fof(f7126,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | ~ spl11_67
    | ~ spl11_436 ),
    inference(subsumption_resolution,[],[f7122,f5872])).

fof(f7122,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) != k1_xboole_0
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | ~ spl11_67 ),
    inference(resolution,[],[f594,f700])).

fof(f700,plain,(
    ! [X4,X5] :
      ( r1_tsep_1(X5,X4)
      | k3_xboole_0(u1_struct_0(X4),u1_struct_0(X5)) != k1_xboole_0
      | ~ l1_struct_0(X4)
      | ~ l1_struct_0(X5) ) ),
    inference(resolution,[],[f378,f166])).

fof(f594,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ spl11_67 ),
    inference(avatar_component_clause,[],[f593])).

fof(f593,plain,
    ( spl11_67
  <=> ~ r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_67])])).

fof(f6675,plain,
    ( spl11_436
    | ~ spl11_404 ),
    inference(avatar_split_clause,[],[f5176,f5032,f5871])).

fof(f5176,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl11_404 ),
    inference(forward_demodulation,[],[f5156,f163])).

fof(f5156,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl11_404 ),
    inference(superposition,[],[f1031,f5033])).

fof(f1031,plain,(
    ! [X14,X15] : k2_xboole_0(k1_xboole_0,k3_xboole_0(X15,X14)) = k3_xboole_0(X14,X15) ),
    inference(forward_demodulation,[],[f1009,f338])).

fof(f338,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f180,f163])).

fof(f1009,plain,(
    ! [X14,X15] : k2_xboole_0(k1_xboole_0,k3_xboole_0(X15,X14)) = k3_xboole_0(X14,k2_xboole_0(k1_xboole_0,X15)) ),
    inference(superposition,[],[f449,f164])).

fof(f164,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',t2_boole)).

fof(f5873,plain,
    ( spl11_436
    | ~ spl11_386 ),
    inference(avatar_split_clause,[],[f4828,f4820,f5871])).

fof(f4820,plain,
    ( spl11_386
  <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_386])])).

fof(f4828,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl11_386 ),
    inference(resolution,[],[f4821,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f111])).

fof(f4821,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl11_386 ),
    inference(avatar_component_clause,[],[f4820])).

fof(f5034,plain,
    ( spl11_404
    | ~ spl11_384 ),
    inference(avatar_split_clause,[],[f4814,f4810,f5032])).

fof(f4810,plain,
    ( spl11_384
  <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_384])])).

fof(f4814,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) = k1_xboole_0
    | ~ spl11_384 ),
    inference(resolution,[],[f4811,f191])).

fof(f4811,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl11_384 ),
    inference(avatar_component_clause,[],[f4810])).

fof(f5027,plain,
    ( spl11_402
    | ~ spl11_378 ),
    inference(avatar_split_clause,[],[f4803,f4758,f5025])).

fof(f4758,plain,
    ( spl11_378
  <=> r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_378])])).

fof(f4803,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl11_378 ),
    inference(resolution,[],[f4759,f191])).

fof(f4759,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl11_378 ),
    inference(avatar_component_clause,[],[f4758])).

fof(f5020,plain,
    ( spl11_400
    | ~ spl11_376 ),
    inference(avatar_split_clause,[],[f4791,f4748,f5018])).

fof(f4748,plain,
    ( spl11_376
  <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_376])])).

fof(f4791,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) = k1_xboole_0
    | ~ spl11_376 ),
    inference(resolution,[],[f4749,f191])).

fof(f4749,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl11_376 ),
    inference(avatar_component_clause,[],[f4748])).

fof(f4824,plain,
    ( spl11_386
    | ~ spl11_60
    | ~ spl11_76
    | ~ spl11_382 ),
    inference(avatar_split_clause,[],[f4823,f4776,f657,f542,f4820])).

fof(f4823,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl11_60
    | ~ spl11_76
    | ~ spl11_382 ),
    inference(subsumption_resolution,[],[f4789,f4777])).

fof(f4789,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_struct_0(sK2)
    | ~ spl11_60
    | ~ spl11_76 ),
    inference(subsumption_resolution,[],[f4787,f658])).

fof(f4787,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl11_60 ),
    inference(resolution,[],[f543,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f4812,plain,
    ( spl11_384
    | ~ spl11_66
    | ~ spl11_76
    | ~ spl11_382 ),
    inference(avatar_split_clause,[],[f4805,f4776,f657,f590,f4810])).

fof(f4805,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl11_66
    | ~ spl11_76
    | ~ spl11_382 ),
    inference(subsumption_resolution,[],[f4726,f4777])).

fof(f4726,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ spl11_66
    | ~ spl11_76 ),
    inference(subsumption_resolution,[],[f4724,f658])).

fof(f4724,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | ~ spl11_66 ),
    inference(resolution,[],[f591,f165])).

fof(f4786,plain,
    ( ~ spl11_32
    | spl11_383 ),
    inference(avatar_contradiction_clause,[],[f4785])).

fof(f4785,plain,
    ( $false
    | ~ spl11_32
    | ~ spl11_383 ),
    inference(subsumption_resolution,[],[f4783,f363])).

fof(f363,plain,
    ( l1_pre_topc(sK2)
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl11_32
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f4783,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl11_383 ),
    inference(resolution,[],[f4780,f168])).

fof(f168,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',dt_l1_pre_topc)).

fof(f4780,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl11_383 ),
    inference(avatar_component_clause,[],[f4779])).

fof(f4779,plain,
    ( spl11_383
  <=> ~ l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_383])])).

fof(f4781,plain,
    ( ~ spl11_383
    | spl11_60
    | ~ spl11_66
    | ~ spl11_76 ),
    inference(avatar_split_clause,[],[f4727,f657,f590,f542,f4779])).

fof(f4727,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl11_66
    | ~ spl11_76 ),
    inference(subsumption_resolution,[],[f4725,f658])).

fof(f4725,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | ~ spl11_66 ),
    inference(resolution,[],[f591,f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',symmetry_r1_tsep_1)).

fof(f4760,plain,
    ( spl11_378
    | ~ spl11_54
    | ~ spl11_74
    | ~ spl11_76 ),
    inference(avatar_split_clause,[],[f4710,f657,f651,f521,f4758])).

fof(f4710,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl11_54
    | ~ spl11_74
    | ~ spl11_76 ),
    inference(subsumption_resolution,[],[f4709,f652])).

fof(f4709,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ l1_struct_0(sK1)
    | ~ spl11_54
    | ~ spl11_76 ),
    inference(subsumption_resolution,[],[f4707,f658])).

fof(f4707,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl11_54 ),
    inference(resolution,[],[f522,f165])).

fof(f4750,plain,
    ( spl11_376
    | ~ spl11_58
    | ~ spl11_74
    | ~ spl11_76 ),
    inference(avatar_split_clause,[],[f4701,f657,f651,f533,f4748])).

fof(f4701,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl11_58
    | ~ spl11_74
    | ~ spl11_76 ),
    inference(subsumption_resolution,[],[f4700,f658])).

fof(f4700,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK3)
    | ~ spl11_58
    | ~ spl11_74 ),
    inference(subsumption_resolution,[],[f4698,f652])).

fof(f4698,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ spl11_58 ),
    inference(resolution,[],[f534,f165])).

fof(f4723,plain,
    ( spl11_60
    | spl11_66
    | spl11_53
    | spl11_57 ),
    inference(avatar_split_clause,[],[f4721,f524,f512,f590,f542])).

fof(f512,plain,
    ( spl11_53
  <=> ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).

fof(f524,plain,
    ( spl11_57
  <=> ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_57])])).

fof(f4721,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3)
    | ~ spl11_53
    | ~ spl11_57 ),
    inference(subsumption_resolution,[],[f4720,f513])).

fof(f513,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl11_53 ),
    inference(avatar_component_clause,[],[f512])).

fof(f4720,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl11_57 ),
    inference(subsumption_resolution,[],[f140,f525])).

fof(f525,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_57 ),
    inference(avatar_component_clause,[],[f524])).

fof(f140,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f104])).

fof(f4713,plain,
    ( spl11_57
    | ~ spl11_76
    | ~ spl11_106
    | ~ spl11_250 ),
    inference(avatar_contradiction_clause,[],[f4712])).

fof(f4712,plain,
    ( $false
    | ~ spl11_57
    | ~ spl11_76
    | ~ spl11_106
    | ~ spl11_250 ),
    inference(unit_resulting_resolution,[],[f658,f933,f2960,f525,f418])).

fof(f933,plain,
    ( l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_106 ),
    inference(avatar_component_clause,[],[f932])).

fof(f932,plain,
    ( spl11_106
  <=> l1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_106])])).

fof(f3706,plain,
    ( spl11_322
    | spl11_7
    | ~ spl11_18
    | ~ spl11_136
    | ~ spl11_166 ),
    inference(avatar_split_clause,[],[f3506,f1814,f1309,f288,f246,f3704])).

fof(f246,plain,
    ( spl11_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f288,plain,
    ( spl11_18
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f1309,plain,
    ( spl11_136
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | u1_struct_0(k1_tsep_1(sK0,sK2,X1)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_136])])).

fof(f1814,plain,
    ( spl11_166
  <=> k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_166])])).

fof(f3506,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_18
    | ~ spl11_136
    | ~ spl11_166 ),
    inference(forward_demodulation,[],[f1359,f1815])).

fof(f1815,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | ~ spl11_166 ),
    inference(avatar_component_clause,[],[f1814])).

fof(f1359,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK1)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_18
    | ~ spl11_136 ),
    inference(subsumption_resolution,[],[f1355,f247])).

fof(f247,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f246])).

fof(f1355,plain,
    ( v2_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(sK0,sK2,sK1)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_18
    | ~ spl11_136 ),
    inference(resolution,[],[f1310,f289])).

fof(f289,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f288])).

fof(f1310,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | u1_struct_0(k1_tsep_1(sK0,sK2,X1)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X1)) )
    | ~ spl11_136 ),
    inference(avatar_component_clause,[],[f1309])).

fof(f3489,plain,
    ( spl11_286
    | spl11_9
    | ~ spl11_20
    | ~ spl11_134 ),
    inference(avatar_split_clause,[],[f1349,f1304,f295,f253,f3487])).

fof(f253,plain,
    ( spl11_9
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f295,plain,
    ( spl11_20
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f1304,plain,
    ( spl11_134
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k1_tsep_1(sK0,sK1,X0)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_134])])).

fof(f1349,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl11_9
    | ~ spl11_20
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1344,f254])).

fof(f254,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f253])).

fof(f1344,plain,
    ( v2_struct_0(sK2)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl11_20
    | ~ spl11_134 ),
    inference(resolution,[],[f1305,f296])).

fof(f296,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f295])).

fof(f1305,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k1_tsep_1(sK0,sK1,X0)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) )
    | ~ spl11_134 ),
    inference(avatar_component_clause,[],[f1304])).

fof(f2961,plain,
    ( spl11_250
    | ~ spl11_176 ),
    inference(avatar_split_clause,[],[f1986,f1966,f2959])).

fof(f1966,plain,
    ( spl11_176
  <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_176])])).

fof(f1986,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = k1_xboole_0
    | ~ spl11_176 ),
    inference(resolution,[],[f1967,f191])).

fof(f1967,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl11_176 ),
    inference(avatar_component_clause,[],[f1966])).

fof(f1973,plain,
    ( spl11_56
    | ~ spl11_52
    | ~ spl11_76
    | ~ spl11_106 ),
    inference(avatar_split_clause,[],[f1970,f932,f657,f515,f527])).

fof(f1970,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_52
    | ~ spl11_76
    | ~ spl11_106 ),
    inference(subsumption_resolution,[],[f1969,f933])).

fof(f1969,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_52
    | ~ spl11_76 ),
    inference(subsumption_resolution,[],[f1948,f658])).

fof(f1948,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_52 ),
    inference(resolution,[],[f516,f190])).

fof(f1968,plain,
    ( spl11_176
    | ~ spl11_56
    | ~ spl11_76
    | ~ spl11_106 ),
    inference(avatar_split_clause,[],[f1950,f932,f657,f527,f1966])).

fof(f1950,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl11_56
    | ~ spl11_76
    | ~ spl11_106 ),
    inference(subsumption_resolution,[],[f1939,f933])).

fof(f1939,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_56
    | ~ spl11_76 ),
    inference(subsumption_resolution,[],[f546,f658])).

fof(f546,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl11_56 ),
    inference(resolution,[],[f528,f165])).

fof(f1913,plain,
    ( ~ spl11_4
    | spl11_111
    | ~ spl11_174 ),
    inference(avatar_contradiction_clause,[],[f1891])).

fof(f1891,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_111
    | ~ spl11_174 ),
    inference(unit_resulting_resolution,[],[f240,f1002,f1866,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',dt_m1_pre_topc)).

fof(f1866,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl11_174 ),
    inference(avatar_component_clause,[],[f1865])).

fof(f1865,plain,
    ( spl11_174
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_174])])).

fof(f1002,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_111 ),
    inference(avatar_component_clause,[],[f1001])).

fof(f1001,plain,
    ( spl11_111
  <=> ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_111])])).

fof(f240,plain,
    ( l1_pre_topc(sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl11_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f1867,plain,
    ( spl11_174
    | spl11_7
    | ~ spl11_18
    | ~ spl11_92
    | ~ spl11_166 ),
    inference(avatar_split_clause,[],[f1852,f1814,f785,f288,f246,f1865])).

fof(f785,plain,
    ( spl11_92
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_pre_topc(k1_tsep_1(sK0,sK2,X1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_92])])).

fof(f1852,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl11_7
    | ~ spl11_18
    | ~ spl11_92
    | ~ spl11_166 ),
    inference(subsumption_resolution,[],[f1851,f289])).

fof(f1851,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl11_7
    | ~ spl11_92
    | ~ spl11_166 ),
    inference(subsumption_resolution,[],[f1846,f247])).

fof(f1846,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl11_92
    | ~ spl11_166 ),
    inference(superposition,[],[f786,f1815])).

fof(f786,plain,
    ( ! [X1] :
        ( m1_pre_topc(k1_tsep_1(sK0,sK2,X1),sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl11_92 ),
    inference(avatar_component_clause,[],[f785])).

fof(f1825,plain,
    ( spl11_166
    | spl11_7
    | ~ spl11_18
    | ~ spl11_124 ),
    inference(avatar_split_clause,[],[f1176,f1141,f288,f246,f1814])).

fof(f1141,plain,
    ( spl11_124
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,sK2) = k1_tsep_1(sK0,sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_124])])).

fof(f1176,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | ~ spl11_7
    | ~ spl11_18
    | ~ spl11_124 ),
    inference(subsumption_resolution,[],[f1172,f247])).

fof(f1172,plain,
    ( v2_struct_0(sK1)
    | k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | ~ spl11_18
    | ~ spl11_124 ),
    inference(resolution,[],[f1142,f289])).

fof(f1142,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,sK2) = k1_tsep_1(sK0,sK2,X1) )
    | ~ spl11_124 ),
    inference(avatar_component_clause,[],[f1141])).

fof(f1311,plain,
    ( spl11_136
    | spl11_1
    | ~ spl11_4
    | spl11_9
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f638,f295,f253,f239,f225,f1309])).

fof(f225,plain,
    ( spl11_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f638,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | u1_struct_0(k1_tsep_1(sK0,sK2,X1)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X1)) )
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f637,f226])).

fof(f226,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f225])).

fof(f637,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | u1_struct_0(k1_tsep_1(sK0,sK2,X1)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X1))
        | v2_struct_0(sK0) )
    | ~ spl11_4
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f636,f240])).

fof(f636,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | u1_struct_0(k1_tsep_1(sK0,sK2,X1)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X1))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f629,f254])).

fof(f629,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | u1_struct_0(k1_tsep_1(sK0,sK2,X1)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X1))
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_20 ),
    inference(resolution,[],[f626,f296])).

fof(f626,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f625,f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',dt_k1_tsep_1)).

fof(f625,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f624,f204])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f624,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f214,f205])).

fof(f205,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f214,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f174])).

fof(f174,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',d2_tsep_1)).

fof(f1306,plain,
    ( spl11_134
    | spl11_1
    | ~ spl11_4
    | spl11_7
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f635,f288,f246,f239,f225,f1304])).

fof(f635,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k1_tsep_1(sK0,sK1,X0)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) )
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f634,f226])).

fof(f634,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k1_tsep_1(sK0,sK1,X0)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f633,f240])).

fof(f633,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k1_tsep_1(sK0,sK1,X0)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_7
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f628,f247])).

fof(f628,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k1_tsep_1(sK0,sK1,X0)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_18 ),
    inference(resolution,[],[f626,f289])).

fof(f1143,plain,
    ( spl11_124
    | spl11_1
    | ~ spl11_4
    | spl11_9
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f606,f295,f253,f239,f225,f1141])).

fof(f606,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,sK2) = k1_tsep_1(sK0,sK2,X1) )
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f605,f226])).

fof(f605,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,sK2) = k1_tsep_1(sK0,sK2,X1)
        | v2_struct_0(sK0) )
    | ~ spl11_4
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f604,f240])).

fof(f604,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,sK2) = k1_tsep_1(sK0,sK2,X1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f597,f254])).

fof(f597,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,sK2) = k1_tsep_1(sK0,sK2,X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_20 ),
    inference(resolution,[],[f202,f296])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',commutativity_k1_tsep_1)).

fof(f1003,plain,
    ( ~ spl11_111
    | spl11_107 ),
    inference(avatar_split_clause,[],[f941,f935,f1001])).

fof(f935,plain,
    ( spl11_107
  <=> ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_107])])).

fof(f941,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_107 ),
    inference(resolution,[],[f936,f168])).

fof(f936,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_107 ),
    inference(avatar_component_clause,[],[f935])).

fof(f937,plain,
    ( ~ spl11_107
    | spl11_52
    | ~ spl11_56
    | ~ spl11_76 ),
    inference(avatar_split_clause,[],[f929,f657,f527,f515,f935])).

fof(f929,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl11_56
    | ~ spl11_76 ),
    inference(subsumption_resolution,[],[f547,f658])).

fof(f547,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl11_56 ),
    inference(resolution,[],[f528,f190])).

fof(f787,plain,
    ( spl11_92
    | spl11_1
    | ~ spl11_4
    | spl11_9
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f569,f295,f253,f239,f225,f785])).

fof(f569,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_pre_topc(k1_tsep_1(sK0,sK2,X1),sK0) )
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f568,f226])).

fof(f568,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_pre_topc(k1_tsep_1(sK0,sK2,X1),sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_4
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f567,f240])).

fof(f567,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_pre_topc(k1_tsep_1(sK0,sK2,X1),sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_9
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f560,f254])).

fof(f560,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_pre_topc(k1_tsep_1(sK0,sK2,X1),sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_20 ),
    inference(resolution,[],[f205,f296])).

fof(f672,plain,
    ( ~ spl11_34
    | spl11_77 ),
    inference(avatar_contradiction_clause,[],[f671])).

fof(f671,plain,
    ( $false
    | ~ spl11_34
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f669,f371])).

fof(f371,plain,
    ( l1_pre_topc(sK3)
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl11_34
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f669,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl11_77 ),
    inference(resolution,[],[f661,f168])).

fof(f661,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl11_77 ),
    inference(avatar_component_clause,[],[f660])).

fof(f660,plain,
    ( spl11_77
  <=> ~ l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_77])])).

fof(f667,plain,
    ( ~ spl11_30
    | spl11_75 ),
    inference(avatar_contradiction_clause,[],[f666])).

fof(f666,plain,
    ( $false
    | ~ spl11_30
    | ~ spl11_75 ),
    inference(subsumption_resolution,[],[f664,f356])).

fof(f356,plain,
    ( l1_pre_topc(sK1)
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl11_30
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f664,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl11_75 ),
    inference(resolution,[],[f655,f168])).

fof(f655,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl11_75 ),
    inference(avatar_component_clause,[],[f654])).

fof(f654,plain,
    ( spl11_75
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_75])])).

fof(f662,plain,
    ( ~ spl11_75
    | ~ spl11_77
    | ~ spl11_54
    | spl11_59 ),
    inference(avatar_split_clause,[],[f649,f530,f521,f660,f654])).

fof(f530,plain,
    ( spl11_59
  <=> ~ r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_59])])).

fof(f649,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl11_54
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f537,f531])).

fof(f531,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ spl11_59 ),
    inference(avatar_component_clause,[],[f530])).

fof(f537,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl11_54 ),
    inference(resolution,[],[f522,f190])).

fof(f535,plain,
    ( spl11_52
    | spl11_54
    | spl11_56
    | spl11_58 ),
    inference(avatar_split_clause,[],[f126,f533,f527,f521,f515])).

fof(f126,plain,
    ( r1_tsep_1(sK3,sK1)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK1,sK3)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f104])).

fof(f372,plain,
    ( spl11_34
    | ~ spl11_22
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f346,f335,f302,f370])).

fof(f302,plain,
    ( spl11_22
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f335,plain,
    ( spl11_28
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f346,plain,
    ( l1_pre_topc(sK3)
    | ~ spl11_22
    | ~ spl11_28 ),
    inference(resolution,[],[f336,f303])).

fof(f303,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f302])).

fof(f336,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f335])).

fof(f364,plain,
    ( spl11_32
    | ~ spl11_20
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f345,f335,f295,f362])).

fof(f345,plain,
    ( l1_pre_topc(sK2)
    | ~ spl11_20
    | ~ spl11_28 ),
    inference(resolution,[],[f336,f296])).

fof(f357,plain,
    ( spl11_30
    | ~ spl11_18
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f344,f335,f288,f355])).

fof(f344,plain,
    ( l1_pre_topc(sK1)
    | ~ spl11_18
    | ~ spl11_28 ),
    inference(resolution,[],[f336,f289])).

fof(f337,plain,
    ( spl11_28
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f328,f239,f335])).

fof(f328,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl11_4 ),
    inference(resolution,[],[f171,f240])).

fof(f320,plain,
    ( spl11_26
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f306,f267,f318])).

fof(f267,plain,
    ( spl11_12
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f306,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl11_12 ),
    inference(backward_demodulation,[],[f305,f268])).

fof(f268,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f267])).

fof(f305,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl11_12 ),
    inference(resolution,[],[f167,f268])).

fof(f304,plain,(
    spl11_22 ),
    inference(avatar_split_clause,[],[f125,f302])).

fof(f125,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f297,plain,(
    spl11_20 ),
    inference(avatar_split_clause,[],[f123,f295])).

fof(f123,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f290,plain,(
    spl11_18 ),
    inference(avatar_split_clause,[],[f121,f288])).

fof(f121,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f269,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f162,f267])).

fof(f162,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',dt_o_0_0_xboole_0)).

fof(f255,plain,(
    ~ spl11_9 ),
    inference(avatar_split_clause,[],[f122,f253])).

fof(f122,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f104])).

fof(f248,plain,(
    ~ spl11_7 ),
    inference(avatar_split_clause,[],[f120,f246])).

fof(f120,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f104])).

fof(f241,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f119,f239])).

fof(f119,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f227,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f117,f225])).

fof(f117,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f104])).
%------------------------------------------------------------------------------
