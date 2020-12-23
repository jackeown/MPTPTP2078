%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  223 ( 469 expanded)
%              Number of leaves         :   40 ( 191 expanded)
%              Depth                    :   13
%              Number of atoms          :  834 (1575 expanded)
%              Number of equality atoms :  141 ( 318 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1961,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f102,f107,f112,f119,f124,f134,f164,f196,f204,f215,f220,f269,f307,f310,f366,f402,f445,f573,f595,f620,f647,f665,f709,f1703,f1960])).

fof(f1960,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | spl2_15
    | ~ spl2_16
    | ~ spl2_25
    | ~ spl2_34
    | ~ spl2_101 ),
    inference(avatar_contradiction_clause,[],[f1959])).

fof(f1959,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | spl2_15
    | ~ spl2_16
    | ~ spl2_25
    | ~ spl2_34
    | ~ spl2_101 ),
    inference(subsumption_resolution,[],[f1958,f195])).

fof(f195,plain,
    ( sK1 != k4_relat_1(sK0)
    | spl2_15 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl2_15
  <=> sK1 = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f1958,plain,
    ( sK1 = k4_relat_1(sK0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_16
    | ~ spl2_25
    | ~ spl2_34
    | ~ spl2_101 ),
    inference(forward_demodulation,[],[f420,f1702])).

fof(f1702,plain,
    ( sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)
    | ~ spl2_101 ),
    inference(avatar_component_clause,[],[f1700])).

fof(f1700,plain,
    ( spl2_101
  <=> sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).

fof(f420,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_16
    | ~ spl2_25
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f415,f60])).

fof(f60,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f415,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_4
    | ~ spl2_16
    | ~ spl2_25
    | ~ spl2_34 ),
    inference(superposition,[],[f401,f397])).

fof(f397,plain,
    ( ! [X0] :
        ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_4
    | ~ spl2_16
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f210,f301])).

fof(f301,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl2_25
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f210,plain,
    ( ! [X0] :
        ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k4_relat_1(sK0)) )
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f207,f75])).

fof(f75,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f207,plain,
    ( ! [X0] :
        ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0))
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k4_relat_1(sK0)) )
    | ~ spl2_16 ),
    inference(superposition,[],[f46,f203])).

fof(f203,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl2_16
  <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f401,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl2_34
  <=> k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f1703,plain,
    ( spl2_101
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_46
    | ~ spl2_48
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f1688,f703,f662,f644,f116,f58,f1700])).

fof(f116,plain,
    ( spl2_9
  <=> sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f644,plain,
    ( spl2_46
  <=> k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k4_relat_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f662,plain,
    ( spl2_48
  <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f703,plain,
    ( spl2_49
  <=> v1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f1688,plain,
    ( sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_46
    | ~ spl2_48
    | ~ spl2_49 ),
    inference(forward_demodulation,[],[f1687,f118])).

fof(f118,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f1687,plain,
    ( k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)
    | ~ spl2_1
    | ~ spl2_46
    | ~ spl2_48
    | ~ spl2_49 ),
    inference(subsumption_resolution,[],[f1675,f60])).

fof(f1675,plain,
    ( k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_1
    | ~ spl2_46
    | ~ spl2_48
    | ~ spl2_49 ),
    inference(superposition,[],[f1669,f646])).

fof(f646,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k4_relat_1(sK1),sK1)
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f644])).

fof(f1669,plain,
    ( ! [X0] :
        ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k5_relat_1(sK1,k5_relat_1(k4_relat_1(sK1),X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_1
    | ~ spl2_48
    | ~ spl2_49 ),
    inference(subsumption_resolution,[],[f700,f704])).

fof(f704,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f703])).

fof(f700,plain,
    ( ! [X0] :
        ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k5_relat_1(sK1,k5_relat_1(k4_relat_1(sK1),X0))
        | ~ v1_relat_1(k4_relat_1(sK1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_1
    | ~ spl2_48 ),
    inference(subsumption_resolution,[],[f691,f60])).

fof(f691,plain,
    ( ! [X0] :
        ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k5_relat_1(sK1,k5_relat_1(k4_relat_1(sK1),X0))
        | ~ v1_relat_1(k4_relat_1(sK1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_48 ),
    inference(superposition,[],[f46,f664])).

fof(f664,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,k4_relat_1(sK1))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f662])).

fof(f709,plain,
    ( ~ spl2_1
    | spl2_49 ),
    inference(avatar_contradiction_clause,[],[f708])).

fof(f708,plain,
    ( $false
    | ~ spl2_1
    | spl2_49 ),
    inference(subsumption_resolution,[],[f707,f60])).

fof(f707,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_49 ),
    inference(resolution,[],[f705,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f705,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | spl2_49 ),
    inference(avatar_component_clause,[],[f703])).

fof(f665,plain,
    ( spl2_48
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_20
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f637,f617,f242,f104,f63,f58,f662])).

fof(f63,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f104,plain,
    ( spl2_7
  <=> k2_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f242,plain,
    ( spl2_20
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f617,plain,
    ( spl2_44
  <=> k2_funct_1(sK1) = k4_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f637,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,k4_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_20
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f611,f619])).

fof(f619,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f617])).

fof(f611,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f610,f106])).

fof(f106,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f610,plain,
    ( k6_relat_1(k1_relat_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f609,f60])).

fof(f609,plain,
    ( ~ v1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl2_2
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f606,f65])).

fof(f65,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f606,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl2_20 ),
    inference(resolution,[],[f244,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f244,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f242])).

fof(f647,plain,
    ( spl2_46
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_20
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f631,f617,f242,f63,f58,f644])).

fof(f631,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k4_relat_1(sK1),sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_20
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f613,f619])).

fof(f613,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f612,f60])).

fof(f612,plain,
    ( ~ v1_relat_1(sK1)
    | k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl2_2
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f607,f65])).

fof(f607,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl2_20 ),
    inference(resolution,[],[f244,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f620,plain,
    ( spl2_44
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f615,f242,f63,f58,f617])).

fof(f615,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f614,f60])).

fof(f614,plain,
    ( ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl2_2
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f608,f65])).

fof(f608,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl2_20 ),
    inference(resolution,[],[f244,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f595,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | spl2_20
    | ~ spl2_38 ),
    inference(avatar_contradiction_clause,[],[f594])).

fof(f594,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | spl2_20
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f593,f243])).

fof(f243,plain,
    ( ~ v2_funct_1(sK1)
    | spl2_20 ),
    inference(avatar_component_clause,[],[f242])).

fof(f593,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f592,f106])).

fof(f592,plain,
    ( k2_relat_1(sK0) != k1_relat_1(sK1)
    | v2_funct_1(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f591,f60])).

fof(f591,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | v2_funct_1(sK1)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f590,f80])).

fof(f80,plain,
    ( v1_funct_1(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f590,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | v2_funct_1(sK1)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f589,f75])).

fof(f589,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | v2_funct_1(sK1)
    | ~ spl2_2
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f585,f65])).

fof(f585,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | v2_funct_1(sK1)
    | ~ spl2_38 ),
    inference(resolution,[],[f476,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f476,plain,
    ( v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f475])).

fof(f475,plain,
    ( spl2_38
  <=> v2_funct_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f573,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_23
    | ~ spl2_26
    | ~ spl2_35
    | spl2_38 ),
    inference(avatar_contradiction_clause,[],[f572])).

fof(f572,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_23
    | ~ spl2_26
    | ~ spl2_35
    | spl2_38 ),
    inference(subsumption_resolution,[],[f463,f477])).

fof(f477,plain,
    ( ~ v2_funct_1(k5_relat_1(sK0,sK1))
    | spl2_38 ),
    inference(avatar_component_clause,[],[f475])).

fof(f463,plain,
    ( v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_23
    | ~ spl2_26
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f462,f133])).

fof(f133,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl2_12
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f462,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,sK1))
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_23
    | ~ spl2_26
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f461,f75])).

fof(f461,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,sK1))
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_23
    | ~ spl2_26
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f460,f268])).

fof(f268,plain,
    ( v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl2_23
  <=> v1_funct_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f460,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,sK1))
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_26
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f459,f306])).

fof(f306,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl2_26
  <=> v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f459,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,sK1))
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f458,f80])).

fof(f458,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,sK1))
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f449,f70])).

fof(f70,plain,
    ( v2_funct_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f449,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,sK1))
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl2_35 ),
    inference(superposition,[],[f53,f444])).

fof(f444,plain,
    ( sK0 = k5_relat_1(k5_relat_1(sK0,sK1),sK0)
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl2_35
  <=> sK0 = k5_relat_1(k5_relat_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f445,plain,
    ( spl2_35
    | ~ spl2_4
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_18
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f440,f300,f217,f201,f121,f73,f442])).

fof(f121,plain,
    ( spl2_10
  <=> sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f217,plain,
    ( spl2_18
  <=> k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f440,plain,
    ( sK0 = k5_relat_1(k5_relat_1(sK0,sK1),sK0)
    | ~ spl2_4
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_18
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f439,f123])).

fof(f123,plain,
    ( sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f439,plain,
    ( k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) = k5_relat_1(k5_relat_1(sK0,sK1),sK0)
    | ~ spl2_4
    | ~ spl2_16
    | ~ spl2_18
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f435,f203])).

fof(f435,plain,
    ( k5_relat_1(sK0,k5_relat_1(k4_relat_1(sK0),sK0)) = k5_relat_1(k5_relat_1(sK0,sK1),sK0)
    | ~ spl2_4
    | ~ spl2_18
    | ~ spl2_25 ),
    inference(resolution,[],[f414,f75])).

fof(f414,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(sK0,k5_relat_1(k4_relat_1(sK0),X0)) = k5_relat_1(k5_relat_1(sK0,sK1),X0) )
    | ~ spl2_4
    | ~ spl2_18
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f234,f301])).

fof(f234,plain,
    ( ! [X0] :
        ( k5_relat_1(sK0,k5_relat_1(k4_relat_1(sK0),X0)) = k5_relat_1(k5_relat_1(sK0,sK1),X0)
        | ~ v1_relat_1(k4_relat_1(sK0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_4
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f229,f75])).

fof(f229,plain,
    ( ! [X0] :
        ( k5_relat_1(sK0,k5_relat_1(k4_relat_1(sK0),X0)) = k5_relat_1(k5_relat_1(sK0,sK1),X0)
        | ~ v1_relat_1(k4_relat_1(sK0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK0) )
    | ~ spl2_18 ),
    inference(superposition,[],[f46,f219])).

fof(f219,plain,
    ( k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f217])).

fof(f402,plain,
    ( spl2_34
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f392,f363,f109,f73,f399])).

fof(f109,plain,
    ( spl2_8
  <=> k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f363,plain,
    ( spl2_33
  <=> k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f392,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f391,f111])).

fof(f111,plain,
    ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f391,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl2_4
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f387,f75])).

fof(f387,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ spl2_33 ),
    inference(superposition,[],[f365,f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f365,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0))))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f363])).

fof(f366,plain,
    ( spl2_33
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f311,f300,f363])).

fof(f311,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0))))
    | ~ spl2_25 ),
    inference(resolution,[],[f301,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f310,plain,
    ( ~ spl2_4
    | spl2_25 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl2_4
    | spl2_25 ),
    inference(subsumption_resolution,[],[f308,f75])).

fof(f308,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_25 ),
    inference(resolution,[],[f302,f42])).

fof(f302,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl2_25 ),
    inference(avatar_component_clause,[],[f300])).

fof(f307,plain,
    ( ~ spl2_25
    | spl2_26
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f230,f217,f212,f78,f73,f304,f300])).

fof(f212,plain,
    ( spl2_17
  <=> v1_funct_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f230,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f226,f214])).

fof(f214,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f212])).

fof(f226,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(superposition,[],[f96,f219])).

fof(f96,plain,
    ( ! [X0] :
        ( v1_relat_1(k5_relat_1(sK0,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f93,f75])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_relat_1(k5_relat_1(sK0,X0)) )
    | ~ spl2_5 ),
    inference(resolution,[],[f80,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f269,plain,
    ( spl2_23
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f181,f78,f73,f63,f58,f266])).

fof(f181,plain,
    ( v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f178,f60])).

fof(f178,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(resolution,[],[f97,f65])).

fof(f97,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | v1_funct_1(k5_relat_1(sK0,X1)) )
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f94,f75])).

fof(f94,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k5_relat_1(sK0,X1)) )
    | ~ spl2_5 ),
    inference(resolution,[],[f80,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f220,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f191,f161,f109,f78,f73,f68,f217])).

fof(f161,plain,
    ( spl2_13
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f191,plain,
    ( k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f190,f111])).

fof(f190,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f189,f163])).

fof(f163,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f189,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f188,f75])).

fof(f188,plain,
    ( ~ v1_relat_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f89,f80])).

fof(f89,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f70,f50])).

fof(f215,plain,
    ( spl2_17
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f169,f161,f78,f73,f212])).

fof(f169,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f168,f75])).

fof(f168,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f167,f80])).

fof(f167,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_13 ),
    inference(superposition,[],[f48,f163])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f204,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f199,f161,f78,f73,f68,f201])).

fof(f199,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f198,f163])).

fof(f198,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f197,f75])).

fof(f197,plain,
    ( ~ v1_relat_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f90,f80])).

fof(f90,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f70,f51])).

fof(f196,plain,
    ( ~ spl2_15
    | spl2_6
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f165,f161,f99,f193])).

fof(f99,plain,
    ( spl2_6
  <=> sK1 = k2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f165,plain,
    ( sK1 != k4_relat_1(sK0)
    | spl2_6
    | ~ spl2_13 ),
    inference(superposition,[],[f101,f163])).

fof(f101,plain,
    ( sK1 != k2_funct_1(sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f164,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f159,f78,f73,f68,f161])).

fof(f159,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f158,f75])).

fof(f158,plain,
    ( ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f91,f80])).

fof(f91,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f70,f49])).

fof(f134,plain,
    ( spl2_12
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f114,f109,f131])).

fof(f114,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl2_8 ),
    inference(superposition,[],[f41,f111])).

fof(f41,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f124,plain,
    ( spl2_10
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f92,f73,f121])).

fof(f92,plain,
    ( sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f75,f43])).

fof(f119,plain,
    ( spl2_9
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f82,f58,f116])).

fof(f82,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_1 ),
    inference(resolution,[],[f60,f43])).

fof(f112,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f36,f109])).

fof(f36,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
                & k2_relat_1(X0) = k1_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f107,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f35,f104])).

fof(f35,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f102,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f37,f99])).

fof(f37,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f33,f63])).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f32,f58])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:40:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.48  % (28474)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (28469)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (28475)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (28489)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (28480)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (28484)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (28479)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (28473)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (28489)Refutation not found, incomplete strategy% (28489)------------------------------
% 0.21/0.51  % (28489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28489)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (28489)Memory used [KB]: 10618
% 0.21/0.51  % (28489)Time elapsed: 0.092 s
% 0.21/0.51  % (28489)------------------------------
% 0.21/0.51  % (28489)------------------------------
% 0.21/0.51  % (28472)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (28476)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (28482)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (28478)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % (28471)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.53  % (28477)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.53  % (28487)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.53  % (28486)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.53  % (28470)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (28481)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (28485)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.55  % (28483)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.56  % (28488)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.59  % (28472)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f1961,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f102,f107,f112,f119,f124,f134,f164,f196,f204,f215,f220,f269,f307,f310,f366,f402,f445,f573,f595,f620,f647,f665,f709,f1703,f1960])).
% 0.21/0.59  fof(f1960,plain,(
% 0.21/0.59    ~spl2_1 | ~spl2_4 | spl2_15 | ~spl2_16 | ~spl2_25 | ~spl2_34 | ~spl2_101),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f1959])).
% 0.21/0.59  fof(f1959,plain,(
% 0.21/0.59    $false | (~spl2_1 | ~spl2_4 | spl2_15 | ~spl2_16 | ~spl2_25 | ~spl2_34 | ~spl2_101)),
% 0.21/0.59    inference(subsumption_resolution,[],[f1958,f195])).
% 0.21/0.59  fof(f195,plain,(
% 0.21/0.59    sK1 != k4_relat_1(sK0) | spl2_15),
% 0.21/0.59    inference(avatar_component_clause,[],[f193])).
% 0.21/0.59  fof(f193,plain,(
% 0.21/0.59    spl2_15 <=> sK1 = k4_relat_1(sK0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.59  fof(f1958,plain,(
% 0.21/0.59    sK1 = k4_relat_1(sK0) | (~spl2_1 | ~spl2_4 | ~spl2_16 | ~spl2_25 | ~spl2_34 | ~spl2_101)),
% 0.21/0.59    inference(forward_demodulation,[],[f420,f1702])).
% 0.21/0.59  fof(f1702,plain,(
% 0.21/0.59    sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) | ~spl2_101),
% 0.21/0.59    inference(avatar_component_clause,[],[f1700])).
% 0.21/0.59  fof(f1700,plain,(
% 0.21/0.59    spl2_101 <=> sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).
% 0.21/0.59  fof(f420,plain,(
% 0.21/0.59    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) | (~spl2_1 | ~spl2_4 | ~spl2_16 | ~spl2_25 | ~spl2_34)),
% 0.21/0.59    inference(subsumption_resolution,[],[f415,f60])).
% 0.21/0.59  fof(f60,plain,(
% 0.21/0.59    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.59    inference(avatar_component_clause,[],[f58])).
% 0.21/0.59  fof(f58,plain,(
% 0.21/0.59    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.59  fof(f415,plain,(
% 0.21/0.59    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) | ~v1_relat_1(sK1) | (~spl2_4 | ~spl2_16 | ~spl2_25 | ~spl2_34)),
% 0.21/0.59    inference(superposition,[],[f401,f397])).
% 0.21/0.59  fof(f397,plain,(
% 0.21/0.59    ( ! [X0] : (k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) | ~v1_relat_1(X0)) ) | (~spl2_4 | ~spl2_16 | ~spl2_25)),
% 0.21/0.59    inference(subsumption_resolution,[],[f210,f301])).
% 0.21/0.59  fof(f301,plain,(
% 0.21/0.59    v1_relat_1(k4_relat_1(sK0)) | ~spl2_25),
% 0.21/0.59    inference(avatar_component_clause,[],[f300])).
% 0.21/0.59  fof(f300,plain,(
% 0.21/0.59    spl2_25 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.59  fof(f210,plain,(
% 0.21/0.59    ( ! [X0] : (k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k4_relat_1(sK0))) ) | (~spl2_4 | ~spl2_16)),
% 0.21/0.59    inference(subsumption_resolution,[],[f207,f75])).
% 0.21/0.59  fof(f75,plain,(
% 0.21/0.59    v1_relat_1(sK0) | ~spl2_4),
% 0.21/0.59    inference(avatar_component_clause,[],[f73])).
% 0.21/0.59  fof(f73,plain,(
% 0.21/0.59    spl2_4 <=> v1_relat_1(sK0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.59  fof(f207,plain,(
% 0.21/0.59    ( ! [X0] : (k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) | ~v1_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_relat_1(k4_relat_1(sK0))) ) | ~spl2_16),
% 0.21/0.59    inference(superposition,[],[f46,f203])).
% 0.21/0.59  fof(f203,plain,(
% 0.21/0.59    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) | ~spl2_16),
% 0.21/0.59    inference(avatar_component_clause,[],[f201])).
% 0.21/0.59  fof(f201,plain,(
% 0.21/0.59    spl2_16 <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.59  fof(f46,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f19])).
% 0.21/0.59  fof(f19,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f3])).
% 0.21/0.59  fof(f3,axiom,(
% 0.21/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.59  fof(f401,plain,(
% 0.21/0.59    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) | ~spl2_34),
% 0.21/0.59    inference(avatar_component_clause,[],[f399])).
% 0.21/0.59  fof(f399,plain,(
% 0.21/0.59    spl2_34 <=> k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.59  fof(f1703,plain,(
% 0.21/0.59    spl2_101 | ~spl2_1 | ~spl2_9 | ~spl2_46 | ~spl2_48 | ~spl2_49),
% 0.21/0.59    inference(avatar_split_clause,[],[f1688,f703,f662,f644,f116,f58,f1700])).
% 0.21/0.59  fof(f116,plain,(
% 0.21/0.59    spl2_9 <=> sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.59  fof(f644,plain,(
% 0.21/0.59    spl2_46 <=> k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k4_relat_1(sK1),sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.21/0.59  fof(f662,plain,(
% 0.21/0.59    spl2_48 <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,k4_relat_1(sK1))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.21/0.59  fof(f703,plain,(
% 0.21/0.59    spl2_49 <=> v1_relat_1(k4_relat_1(sK1))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 0.21/0.59  fof(f1688,plain,(
% 0.21/0.59    sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) | (~spl2_1 | ~spl2_9 | ~spl2_46 | ~spl2_48 | ~spl2_49)),
% 0.21/0.59    inference(forward_demodulation,[],[f1687,f118])).
% 0.21/0.59  fof(f118,plain,(
% 0.21/0.59    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~spl2_9),
% 0.21/0.59    inference(avatar_component_clause,[],[f116])).
% 0.21/0.59  fof(f1687,plain,(
% 0.21/0.59    k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) | (~spl2_1 | ~spl2_46 | ~spl2_48 | ~spl2_49)),
% 0.21/0.59    inference(subsumption_resolution,[],[f1675,f60])).
% 0.21/0.59  fof(f1675,plain,(
% 0.21/0.59    k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) | ~v1_relat_1(sK1) | (~spl2_1 | ~spl2_46 | ~spl2_48 | ~spl2_49)),
% 0.21/0.59    inference(superposition,[],[f1669,f646])).
% 0.21/0.59  fof(f646,plain,(
% 0.21/0.59    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k4_relat_1(sK1),sK1) | ~spl2_46),
% 0.21/0.59    inference(avatar_component_clause,[],[f644])).
% 0.21/0.59  fof(f1669,plain,(
% 0.21/0.59    ( ! [X0] : (k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k5_relat_1(sK1,k5_relat_1(k4_relat_1(sK1),X0)) | ~v1_relat_1(X0)) ) | (~spl2_1 | ~spl2_48 | ~spl2_49)),
% 0.21/0.59    inference(subsumption_resolution,[],[f700,f704])).
% 0.21/0.59  fof(f704,plain,(
% 0.21/0.59    v1_relat_1(k4_relat_1(sK1)) | ~spl2_49),
% 0.21/0.59    inference(avatar_component_clause,[],[f703])).
% 0.21/0.59  fof(f700,plain,(
% 0.21/0.59    ( ! [X0] : (k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k5_relat_1(sK1,k5_relat_1(k4_relat_1(sK1),X0)) | ~v1_relat_1(k4_relat_1(sK1)) | ~v1_relat_1(X0)) ) | (~spl2_1 | ~spl2_48)),
% 0.21/0.59    inference(subsumption_resolution,[],[f691,f60])).
% 0.21/0.59  fof(f691,plain,(
% 0.21/0.59    ( ! [X0] : (k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0) = k5_relat_1(sK1,k5_relat_1(k4_relat_1(sK1),X0)) | ~v1_relat_1(k4_relat_1(sK1)) | ~v1_relat_1(X0) | ~v1_relat_1(sK1)) ) | ~spl2_48),
% 0.21/0.59    inference(superposition,[],[f46,f664])).
% 0.21/0.59  fof(f664,plain,(
% 0.21/0.59    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,k4_relat_1(sK1)) | ~spl2_48),
% 0.21/0.59    inference(avatar_component_clause,[],[f662])).
% 0.21/0.59  fof(f709,plain,(
% 0.21/0.59    ~spl2_1 | spl2_49),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f708])).
% 0.21/0.59  fof(f708,plain,(
% 0.21/0.59    $false | (~spl2_1 | spl2_49)),
% 0.21/0.59    inference(subsumption_resolution,[],[f707,f60])).
% 0.21/0.59  fof(f707,plain,(
% 0.21/0.59    ~v1_relat_1(sK1) | spl2_49),
% 0.21/0.59    inference(resolution,[],[f705,f42])).
% 0.21/0.59  fof(f42,plain,(
% 0.21/0.59    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f16])).
% 0.21/0.59  fof(f16,plain,(
% 0.21/0.59    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.59  fof(f705,plain,(
% 0.21/0.59    ~v1_relat_1(k4_relat_1(sK1)) | spl2_49),
% 0.21/0.59    inference(avatar_component_clause,[],[f703])).
% 0.21/0.59  fof(f665,plain,(
% 0.21/0.59    spl2_48 | ~spl2_1 | ~spl2_2 | ~spl2_7 | ~spl2_20 | ~spl2_44),
% 0.21/0.59    inference(avatar_split_clause,[],[f637,f617,f242,f104,f63,f58,f662])).
% 0.21/0.59  fof(f63,plain,(
% 0.21/0.59    spl2_2 <=> v1_funct_1(sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.59  fof(f104,plain,(
% 0.21/0.59    spl2_7 <=> k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.59  fof(f242,plain,(
% 0.21/0.59    spl2_20 <=> v2_funct_1(sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.59  fof(f617,plain,(
% 0.21/0.59    spl2_44 <=> k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.21/0.59  fof(f637,plain,(
% 0.21/0.59    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,k4_relat_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_7 | ~spl2_20 | ~spl2_44)),
% 0.21/0.59    inference(forward_demodulation,[],[f611,f619])).
% 0.21/0.59  fof(f619,plain,(
% 0.21/0.59    k2_funct_1(sK1) = k4_relat_1(sK1) | ~spl2_44),
% 0.21/0.59    inference(avatar_component_clause,[],[f617])).
% 0.21/0.59  fof(f611,plain,(
% 0.21/0.59    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,k2_funct_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_7 | ~spl2_20)),
% 0.21/0.59    inference(forward_demodulation,[],[f610,f106])).
% 0.21/0.59  fof(f106,plain,(
% 0.21/0.59    k2_relat_1(sK0) = k1_relat_1(sK1) | ~spl2_7),
% 0.21/0.59    inference(avatar_component_clause,[],[f104])).
% 0.21/0.59  fof(f610,plain,(
% 0.21/0.59    k6_relat_1(k1_relat_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_20)),
% 0.21/0.59    inference(subsumption_resolution,[],[f609,f60])).
% 0.21/0.59  fof(f609,plain,(
% 0.21/0.59    ~v1_relat_1(sK1) | k6_relat_1(k1_relat_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1)) | (~spl2_2 | ~spl2_20)),
% 0.21/0.59    inference(subsumption_resolution,[],[f606,f65])).
% 0.21/0.59  fof(f65,plain,(
% 0.21/0.59    v1_funct_1(sK1) | ~spl2_2),
% 0.21/0.59    inference(avatar_component_clause,[],[f63])).
% 0.21/0.59  fof(f606,plain,(
% 0.21/0.59    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k6_relat_1(k1_relat_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~spl2_20),
% 0.21/0.59    inference(resolution,[],[f244,f50])).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f25])).
% 0.21/0.59  fof(f25,plain,(
% 0.21/0.59    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(flattening,[],[f24])).
% 0.21/0.59  fof(f24,plain,(
% 0.21/0.59    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f11])).
% 0.21/0.59  fof(f11,axiom,(
% 0.21/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.59  fof(f244,plain,(
% 0.21/0.59    v2_funct_1(sK1) | ~spl2_20),
% 0.21/0.59    inference(avatar_component_clause,[],[f242])).
% 0.21/0.59  fof(f647,plain,(
% 0.21/0.59    spl2_46 | ~spl2_1 | ~spl2_2 | ~spl2_20 | ~spl2_44),
% 0.21/0.59    inference(avatar_split_clause,[],[f631,f617,f242,f63,f58,f644])).
% 0.21/0.59  fof(f631,plain,(
% 0.21/0.59    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k4_relat_1(sK1),sK1) | (~spl2_1 | ~spl2_2 | ~spl2_20 | ~spl2_44)),
% 0.21/0.59    inference(forward_demodulation,[],[f613,f619])).
% 0.21/0.59  fof(f613,plain,(
% 0.21/0.59    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k2_funct_1(sK1),sK1) | (~spl2_1 | ~spl2_2 | ~spl2_20)),
% 0.21/0.59    inference(subsumption_resolution,[],[f612,f60])).
% 0.21/0.59  fof(f612,plain,(
% 0.21/0.59    ~v1_relat_1(sK1) | k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k2_funct_1(sK1),sK1) | (~spl2_2 | ~spl2_20)),
% 0.21/0.59    inference(subsumption_resolution,[],[f607,f65])).
% 0.21/0.59  fof(f607,plain,(
% 0.21/0.59    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k2_funct_1(sK1),sK1) | ~spl2_20),
% 0.21/0.59    inference(resolution,[],[f244,f51])).
% 0.21/0.59  fof(f51,plain,(
% 0.21/0.59    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f25])).
% 0.21/0.59  fof(f620,plain,(
% 0.21/0.59    spl2_44 | ~spl2_1 | ~spl2_2 | ~spl2_20),
% 0.21/0.59    inference(avatar_split_clause,[],[f615,f242,f63,f58,f617])).
% 0.21/0.59  fof(f615,plain,(
% 0.21/0.59    k2_funct_1(sK1) = k4_relat_1(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_20)),
% 0.21/0.59    inference(subsumption_resolution,[],[f614,f60])).
% 0.21/0.59  fof(f614,plain,(
% 0.21/0.59    ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1) | (~spl2_2 | ~spl2_20)),
% 0.21/0.59    inference(subsumption_resolution,[],[f608,f65])).
% 0.21/0.59  fof(f608,plain,(
% 0.21/0.59    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1) | ~spl2_20),
% 0.21/0.59    inference(resolution,[],[f244,f49])).
% 0.21/0.59  fof(f49,plain,(
% 0.21/0.59    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f23])).
% 0.21/0.59  fof(f23,plain,(
% 0.21/0.59    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(flattening,[],[f22])).
% 0.21/0.59  fof(f22,plain,(
% 0.21/0.59    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f6])).
% 0.21/0.59  fof(f6,axiom,(
% 0.21/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.59  fof(f595,plain,(
% 0.21/0.59    ~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7 | spl2_20 | ~spl2_38),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f594])).
% 0.21/0.59  fof(f594,plain,(
% 0.21/0.59    $false | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7 | spl2_20 | ~spl2_38)),
% 0.21/0.59    inference(subsumption_resolution,[],[f593,f243])).
% 0.21/0.59  fof(f243,plain,(
% 0.21/0.59    ~v2_funct_1(sK1) | spl2_20),
% 0.21/0.59    inference(avatar_component_clause,[],[f242])).
% 0.21/0.59  fof(f593,plain,(
% 0.21/0.59    v2_funct_1(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_38)),
% 0.21/0.59    inference(subsumption_resolution,[],[f592,f106])).
% 0.21/0.59  fof(f592,plain,(
% 0.21/0.59    k2_relat_1(sK0) != k1_relat_1(sK1) | v2_funct_1(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_38)),
% 0.21/0.59    inference(subsumption_resolution,[],[f591,f60])).
% 0.21/0.59  fof(f591,plain,(
% 0.21/0.59    ~v1_relat_1(sK1) | k2_relat_1(sK0) != k1_relat_1(sK1) | v2_funct_1(sK1) | (~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_38)),
% 0.21/0.59    inference(subsumption_resolution,[],[f590,f80])).
% 0.21/0.59  fof(f80,plain,(
% 0.21/0.59    v1_funct_1(sK0) | ~spl2_5),
% 0.21/0.59    inference(avatar_component_clause,[],[f78])).
% 0.21/0.59  fof(f78,plain,(
% 0.21/0.59    spl2_5 <=> v1_funct_1(sK0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.59  fof(f590,plain,(
% 0.21/0.59    ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | k2_relat_1(sK0) != k1_relat_1(sK1) | v2_funct_1(sK1) | (~spl2_2 | ~spl2_4 | ~spl2_38)),
% 0.21/0.59    inference(subsumption_resolution,[],[f589,f75])).
% 0.21/0.59  fof(f589,plain,(
% 0.21/0.59    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | k2_relat_1(sK0) != k1_relat_1(sK1) | v2_funct_1(sK1) | (~spl2_2 | ~spl2_38)),
% 0.21/0.59    inference(subsumption_resolution,[],[f585,f65])).
% 0.21/0.59  fof(f585,plain,(
% 0.21/0.59    ~v1_funct_1(sK1) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | k2_relat_1(sK0) != k1_relat_1(sK1) | v2_funct_1(sK1) | ~spl2_38),
% 0.21/0.59    inference(resolution,[],[f476,f54])).
% 0.21/0.59  fof(f54,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | v2_funct_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f29])).
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(flattening,[],[f28])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f9])).
% 0.21/0.59  fof(f9,axiom,(
% 0.21/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 0.21/0.59  fof(f476,plain,(
% 0.21/0.59    v2_funct_1(k5_relat_1(sK0,sK1)) | ~spl2_38),
% 0.21/0.59    inference(avatar_component_clause,[],[f475])).
% 0.21/0.59  fof(f475,plain,(
% 0.21/0.59    spl2_38 <=> v2_funct_1(k5_relat_1(sK0,sK1))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.21/0.59  fof(f573,plain,(
% 0.21/0.59    ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_12 | ~spl2_23 | ~spl2_26 | ~spl2_35 | spl2_38),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f572])).
% 0.21/0.59  fof(f572,plain,(
% 0.21/0.59    $false | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_12 | ~spl2_23 | ~spl2_26 | ~spl2_35 | spl2_38)),
% 0.21/0.59    inference(subsumption_resolution,[],[f463,f477])).
% 0.21/0.59  fof(f477,plain,(
% 0.21/0.59    ~v2_funct_1(k5_relat_1(sK0,sK1)) | spl2_38),
% 0.21/0.59    inference(avatar_component_clause,[],[f475])).
% 0.21/0.59  fof(f463,plain,(
% 0.21/0.59    v2_funct_1(k5_relat_1(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_12 | ~spl2_23 | ~spl2_26 | ~spl2_35)),
% 0.21/0.59    inference(subsumption_resolution,[],[f462,f133])).
% 0.21/0.59  fof(f133,plain,(
% 0.21/0.59    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,sK1)) | ~spl2_12),
% 0.21/0.59    inference(avatar_component_clause,[],[f131])).
% 0.21/0.59  fof(f131,plain,(
% 0.21/0.59    spl2_12 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,sK1))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.59  fof(f462,plain,(
% 0.21/0.59    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,sK1)) | v2_funct_1(k5_relat_1(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_23 | ~spl2_26 | ~spl2_35)),
% 0.21/0.59    inference(subsumption_resolution,[],[f461,f75])).
% 0.21/0.59  fof(f461,plain,(
% 0.21/0.59    ~v1_relat_1(sK0) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,sK1)) | v2_funct_1(k5_relat_1(sK0,sK1)) | (~spl2_3 | ~spl2_5 | ~spl2_23 | ~spl2_26 | ~spl2_35)),
% 0.21/0.59    inference(subsumption_resolution,[],[f460,f268])).
% 0.21/0.59  fof(f268,plain,(
% 0.21/0.59    v1_funct_1(k5_relat_1(sK0,sK1)) | ~spl2_23),
% 0.21/0.59    inference(avatar_component_clause,[],[f266])).
% 0.21/0.59  fof(f266,plain,(
% 0.21/0.59    spl2_23 <=> v1_funct_1(k5_relat_1(sK0,sK1))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.59  fof(f460,plain,(
% 0.21/0.59    ~v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK0) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,sK1)) | v2_funct_1(k5_relat_1(sK0,sK1)) | (~spl2_3 | ~spl2_5 | ~spl2_26 | ~spl2_35)),
% 0.21/0.59    inference(subsumption_resolution,[],[f459,f306])).
% 0.21/0.59  fof(f306,plain,(
% 0.21/0.59    v1_relat_1(k5_relat_1(sK0,sK1)) | ~spl2_26),
% 0.21/0.59    inference(avatar_component_clause,[],[f304])).
% 0.21/0.59  fof(f304,plain,(
% 0.21/0.59    spl2_26 <=> v1_relat_1(k5_relat_1(sK0,sK1))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.59  fof(f459,plain,(
% 0.21/0.59    ~v1_relat_1(k5_relat_1(sK0,sK1)) | ~v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK0) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,sK1)) | v2_funct_1(k5_relat_1(sK0,sK1)) | (~spl2_3 | ~spl2_5 | ~spl2_35)),
% 0.21/0.59    inference(subsumption_resolution,[],[f458,f80])).
% 0.21/0.59  fof(f458,plain,(
% 0.21/0.59    ~v1_funct_1(sK0) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | ~v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK0) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,sK1)) | v2_funct_1(k5_relat_1(sK0,sK1)) | (~spl2_3 | ~spl2_35)),
% 0.21/0.59    inference(subsumption_resolution,[],[f449,f70])).
% 0.21/0.59  fof(f70,plain,(
% 0.21/0.59    v2_funct_1(sK0) | ~spl2_3),
% 0.21/0.59    inference(avatar_component_clause,[],[f68])).
% 0.21/0.59  fof(f68,plain,(
% 0.21/0.59    spl2_3 <=> v2_funct_1(sK0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.59  fof(f449,plain,(
% 0.21/0.59    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | ~v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK0) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,sK1)) | v2_funct_1(k5_relat_1(sK0,sK1)) | ~spl2_35),
% 0.21/0.59    inference(superposition,[],[f53,f444])).
% 0.21/0.59  fof(f444,plain,(
% 0.21/0.59    sK0 = k5_relat_1(k5_relat_1(sK0,sK1),sK0) | ~spl2_35),
% 0.21/0.59    inference(avatar_component_clause,[],[f442])).
% 0.21/0.59  fof(f442,plain,(
% 0.21/0.59    spl2_35 <=> sK0 = k5_relat_1(k5_relat_1(sK0,sK1),sK0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.21/0.59  fof(f53,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | v2_funct_1(X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f29])).
% 0.21/0.59  fof(f445,plain,(
% 0.21/0.59    spl2_35 | ~spl2_4 | ~spl2_10 | ~spl2_16 | ~spl2_18 | ~spl2_25),
% 0.21/0.59    inference(avatar_split_clause,[],[f440,f300,f217,f201,f121,f73,f442])).
% 0.21/0.59  fof(f121,plain,(
% 0.21/0.59    spl2_10 <=> sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.59  fof(f217,plain,(
% 0.21/0.59    spl2_18 <=> k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k4_relat_1(sK0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.59  fof(f440,plain,(
% 0.21/0.59    sK0 = k5_relat_1(k5_relat_1(sK0,sK1),sK0) | (~spl2_4 | ~spl2_10 | ~spl2_16 | ~spl2_18 | ~spl2_25)),
% 0.21/0.59    inference(forward_demodulation,[],[f439,f123])).
% 0.21/0.59  fof(f123,plain,(
% 0.21/0.59    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) | ~spl2_10),
% 0.21/0.59    inference(avatar_component_clause,[],[f121])).
% 0.21/0.59  fof(f439,plain,(
% 0.21/0.59    k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) = k5_relat_1(k5_relat_1(sK0,sK1),sK0) | (~spl2_4 | ~spl2_16 | ~spl2_18 | ~spl2_25)),
% 0.21/0.59    inference(forward_demodulation,[],[f435,f203])).
% 0.21/0.59  fof(f435,plain,(
% 0.21/0.59    k5_relat_1(sK0,k5_relat_1(k4_relat_1(sK0),sK0)) = k5_relat_1(k5_relat_1(sK0,sK1),sK0) | (~spl2_4 | ~spl2_18 | ~spl2_25)),
% 0.21/0.59    inference(resolution,[],[f414,f75])).
% 0.21/0.59  fof(f414,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(sK0,k5_relat_1(k4_relat_1(sK0),X0)) = k5_relat_1(k5_relat_1(sK0,sK1),X0)) ) | (~spl2_4 | ~spl2_18 | ~spl2_25)),
% 0.21/0.59    inference(subsumption_resolution,[],[f234,f301])).
% 0.21/0.59  fof(f234,plain,(
% 0.21/0.59    ( ! [X0] : (k5_relat_1(sK0,k5_relat_1(k4_relat_1(sK0),X0)) = k5_relat_1(k5_relat_1(sK0,sK1),X0) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(X0)) ) | (~spl2_4 | ~spl2_18)),
% 0.21/0.59    inference(subsumption_resolution,[],[f229,f75])).
% 0.21/0.59  fof(f229,plain,(
% 0.21/0.59    ( ! [X0] : (k5_relat_1(sK0,k5_relat_1(k4_relat_1(sK0),X0)) = k5_relat_1(k5_relat_1(sK0,sK1),X0) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) ) | ~spl2_18),
% 0.21/0.59    inference(superposition,[],[f46,f219])).
% 0.21/0.59  fof(f219,plain,(
% 0.21/0.59    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k4_relat_1(sK0)) | ~spl2_18),
% 0.21/0.59    inference(avatar_component_clause,[],[f217])).
% 0.21/0.59  fof(f402,plain,(
% 0.21/0.59    spl2_34 | ~spl2_4 | ~spl2_8 | ~spl2_33),
% 0.21/0.59    inference(avatar_split_clause,[],[f392,f363,f109,f73,f399])).
% 0.21/0.59  fof(f109,plain,(
% 0.21/0.59    spl2_8 <=> k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.59  fof(f363,plain,(
% 0.21/0.59    spl2_33 <=> k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0))))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.21/0.59  fof(f392,plain,(
% 0.21/0.59    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) | (~spl2_4 | ~spl2_8 | ~spl2_33)),
% 0.21/0.59    inference(forward_demodulation,[],[f391,f111])).
% 0.21/0.59  fof(f111,plain,(
% 0.21/0.59    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) | ~spl2_8),
% 0.21/0.59    inference(avatar_component_clause,[],[f109])).
% 0.21/0.59  fof(f391,plain,(
% 0.21/0.59    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) | (~spl2_4 | ~spl2_33)),
% 0.21/0.59    inference(subsumption_resolution,[],[f387,f75])).
% 0.21/0.59  fof(f387,plain,(
% 0.21/0.59    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) | ~v1_relat_1(sK0) | ~spl2_33),
% 0.21/0.59    inference(superposition,[],[f365,f45])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f18])).
% 0.21/0.59  fof(f18,plain,(
% 0.21/0.59    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f2])).
% 0.21/0.59  fof(f2,axiom,(
% 0.21/0.59    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.59  fof(f365,plain,(
% 0.21/0.59    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0)))) | ~spl2_33),
% 0.21/0.59    inference(avatar_component_clause,[],[f363])).
% 0.21/0.59  fof(f366,plain,(
% 0.21/0.59    spl2_33 | ~spl2_25),
% 0.21/0.59    inference(avatar_split_clause,[],[f311,f300,f363])).
% 0.21/0.59  fof(f311,plain,(
% 0.21/0.59    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0)))) | ~spl2_25),
% 0.21/0.59    inference(resolution,[],[f301,f43])).
% 0.21/0.59  fof(f43,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.21/0.59    inference(cnf_transformation,[],[f17])).
% 0.21/0.59  fof(f17,plain,(
% 0.21/0.59    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.59  fof(f310,plain,(
% 0.21/0.59    ~spl2_4 | spl2_25),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f309])).
% 0.21/0.59  fof(f309,plain,(
% 0.21/0.59    $false | (~spl2_4 | spl2_25)),
% 0.21/0.59    inference(subsumption_resolution,[],[f308,f75])).
% 0.21/0.59  fof(f308,plain,(
% 0.21/0.59    ~v1_relat_1(sK0) | spl2_25),
% 0.21/0.59    inference(resolution,[],[f302,f42])).
% 0.21/0.59  fof(f302,plain,(
% 0.21/0.59    ~v1_relat_1(k4_relat_1(sK0)) | spl2_25),
% 0.21/0.59    inference(avatar_component_clause,[],[f300])).
% 0.21/0.59  fof(f307,plain,(
% 0.21/0.59    ~spl2_25 | spl2_26 | ~spl2_4 | ~spl2_5 | ~spl2_17 | ~spl2_18),
% 0.21/0.59    inference(avatar_split_clause,[],[f230,f217,f212,f78,f73,f304,f300])).
% 0.21/0.59  fof(f212,plain,(
% 0.21/0.59    spl2_17 <=> v1_funct_1(k4_relat_1(sK0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.59  fof(f230,plain,(
% 0.21/0.59    v1_relat_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl2_4 | ~spl2_5 | ~spl2_17 | ~spl2_18)),
% 0.21/0.59    inference(subsumption_resolution,[],[f226,f214])).
% 0.21/0.59  fof(f214,plain,(
% 0.21/0.59    v1_funct_1(k4_relat_1(sK0)) | ~spl2_17),
% 0.21/0.59    inference(avatar_component_clause,[],[f212])).
% 0.21/0.59  fof(f226,plain,(
% 0.21/0.59    v1_relat_1(k5_relat_1(sK0,sK1)) | ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl2_4 | ~spl2_5 | ~spl2_18)),
% 0.21/0.59    inference(superposition,[],[f96,f219])).
% 0.21/0.59  fof(f96,plain,(
% 0.21/0.59    ( ! [X0] : (v1_relat_1(k5_relat_1(sK0,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_4 | ~spl2_5)),
% 0.21/0.59    inference(subsumption_resolution,[],[f93,f75])).
% 0.21/0.59  fof(f93,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k5_relat_1(sK0,X0))) ) | ~spl2_5),
% 0.21/0.59    inference(resolution,[],[f80,f55])).
% 0.21/0.59  fof(f55,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f31])).
% 0.21/0.59  fof(f31,plain,(
% 0.21/0.59    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(flattening,[],[f30])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f8])).
% 0.21/0.59  fof(f8,axiom,(
% 0.21/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.21/0.59  fof(f269,plain,(
% 0.21/0.59    spl2_23 | ~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5),
% 0.21/0.59    inference(avatar_split_clause,[],[f181,f78,f73,f63,f58,f266])).
% 0.21/0.59  fof(f181,plain,(
% 0.21/0.59    v1_funct_1(k5_relat_1(sK0,sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5)),
% 0.21/0.59    inference(subsumption_resolution,[],[f178,f60])).
% 0.21/0.59  fof(f178,plain,(
% 0.21/0.59    ~v1_relat_1(sK1) | v1_funct_1(k5_relat_1(sK0,sK1)) | (~spl2_2 | ~spl2_4 | ~spl2_5)),
% 0.21/0.59    inference(resolution,[],[f97,f65])).
% 0.21/0.59  fof(f97,plain,(
% 0.21/0.59    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_1(k5_relat_1(sK0,X1))) ) | (~spl2_4 | ~spl2_5)),
% 0.21/0.59    inference(subsumption_resolution,[],[f94,f75])).
% 0.21/0.59  fof(f94,plain,(
% 0.21/0.59    ( ! [X1] : (~v1_relat_1(sK0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | v1_funct_1(k5_relat_1(sK0,X1))) ) | ~spl2_5),
% 0.21/0.59    inference(resolution,[],[f80,f56])).
% 0.21/0.59  fof(f56,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | v1_funct_1(k5_relat_1(X0,X1))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f31])).
% 0.21/0.59  fof(f220,plain,(
% 0.21/0.59    spl2_18 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_8 | ~spl2_13),
% 0.21/0.59    inference(avatar_split_clause,[],[f191,f161,f109,f78,f73,f68,f217])).
% 0.21/0.59  fof(f161,plain,(
% 0.21/0.59    spl2_13 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.59  fof(f191,plain,(
% 0.21/0.59    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k4_relat_1(sK0)) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_8 | ~spl2_13)),
% 0.21/0.59    inference(forward_demodulation,[],[f190,f111])).
% 0.21/0.59  fof(f190,plain,(
% 0.21/0.59    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0)) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_13)),
% 0.21/0.59    inference(forward_demodulation,[],[f189,f163])).
% 0.21/0.59  fof(f163,plain,(
% 0.21/0.59    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl2_13),
% 0.21/0.59    inference(avatar_component_clause,[],[f161])).
% 0.21/0.59  fof(f189,plain,(
% 0.21/0.59    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.21/0.59    inference(subsumption_resolution,[],[f188,f75])).
% 0.21/0.59  fof(f188,plain,(
% 0.21/0.59    ~v1_relat_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) | (~spl2_3 | ~spl2_5)),
% 0.21/0.59    inference(subsumption_resolution,[],[f89,f80])).
% 0.21/0.59  fof(f89,plain,(
% 0.21/0.59    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) | ~spl2_3),
% 0.21/0.59    inference(resolution,[],[f70,f50])).
% 0.21/0.59  fof(f215,plain,(
% 0.21/0.59    spl2_17 | ~spl2_4 | ~spl2_5 | ~spl2_13),
% 0.21/0.59    inference(avatar_split_clause,[],[f169,f161,f78,f73,f212])).
% 0.21/0.59  fof(f169,plain,(
% 0.21/0.59    v1_funct_1(k4_relat_1(sK0)) | (~spl2_4 | ~spl2_5 | ~spl2_13)),
% 0.21/0.59    inference(subsumption_resolution,[],[f168,f75])).
% 0.21/0.59  fof(f168,plain,(
% 0.21/0.59    v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl2_5 | ~spl2_13)),
% 0.21/0.59    inference(subsumption_resolution,[],[f167,f80])).
% 0.21/0.59  fof(f167,plain,(
% 0.21/0.59    v1_funct_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_13),
% 0.21/0.59    inference(superposition,[],[f48,f163])).
% 0.21/0.59  fof(f48,plain,(
% 0.21/0.59    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f21])).
% 0.21/0.59  fof(f21,plain,(
% 0.21/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(flattening,[],[f20])).
% 0.21/0.59  fof(f20,plain,(
% 0.21/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,axiom,(
% 0.21/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.59  fof(f204,plain,(
% 0.21/0.59    spl2_16 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_13),
% 0.21/0.59    inference(avatar_split_clause,[],[f199,f161,f78,f73,f68,f201])).
% 0.21/0.59  fof(f199,plain,(
% 0.21/0.59    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_13)),
% 0.21/0.59    inference(forward_demodulation,[],[f198,f163])).
% 0.21/0.59  fof(f198,plain,(
% 0.21/0.59    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.21/0.59    inference(subsumption_resolution,[],[f197,f75])).
% 0.21/0.59  fof(f197,plain,(
% 0.21/0.59    ~v1_relat_1(sK0) | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) | (~spl2_3 | ~spl2_5)),
% 0.21/0.59    inference(subsumption_resolution,[],[f90,f80])).
% 0.21/0.59  fof(f90,plain,(
% 0.21/0.59    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) | ~spl2_3),
% 0.21/0.59    inference(resolution,[],[f70,f51])).
% 0.21/0.59  fof(f196,plain,(
% 0.21/0.59    ~spl2_15 | spl2_6 | ~spl2_13),
% 0.21/0.59    inference(avatar_split_clause,[],[f165,f161,f99,f193])).
% 0.21/0.59  fof(f99,plain,(
% 0.21/0.59    spl2_6 <=> sK1 = k2_funct_1(sK0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.59  fof(f165,plain,(
% 0.21/0.59    sK1 != k4_relat_1(sK0) | (spl2_6 | ~spl2_13)),
% 0.21/0.59    inference(superposition,[],[f101,f163])).
% 0.21/0.59  fof(f101,plain,(
% 0.21/0.59    sK1 != k2_funct_1(sK0) | spl2_6),
% 0.21/0.59    inference(avatar_component_clause,[],[f99])).
% 0.21/0.59  fof(f164,plain,(
% 0.21/0.59    spl2_13 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 0.21/0.59    inference(avatar_split_clause,[],[f159,f78,f73,f68,f161])).
% 0.21/0.59  fof(f159,plain,(
% 0.21/0.59    k2_funct_1(sK0) = k4_relat_1(sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.21/0.59    inference(subsumption_resolution,[],[f158,f75])).
% 0.21/0.59  fof(f158,plain,(
% 0.21/0.59    ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0) | (~spl2_3 | ~spl2_5)),
% 0.21/0.59    inference(subsumption_resolution,[],[f91,f80])).
% 0.21/0.59  fof(f91,plain,(
% 0.21/0.59    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl2_3),
% 0.21/0.59    inference(resolution,[],[f70,f49])).
% 0.21/0.59  fof(f134,plain,(
% 0.21/0.59    spl2_12 | ~spl2_8),
% 0.21/0.59    inference(avatar_split_clause,[],[f114,f109,f131])).
% 0.21/0.59  fof(f114,plain,(
% 0.21/0.59    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,sK1)) | ~spl2_8),
% 0.21/0.59    inference(superposition,[],[f41,f111])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.59    inference(cnf_transformation,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.59  fof(f124,plain,(
% 0.21/0.59    spl2_10 | ~spl2_4),
% 0.21/0.59    inference(avatar_split_clause,[],[f92,f73,f121])).
% 0.21/0.59  fof(f92,plain,(
% 0.21/0.59    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) | ~spl2_4),
% 0.21/0.59    inference(resolution,[],[f75,f43])).
% 0.21/0.59  fof(f119,plain,(
% 0.21/0.59    spl2_9 | ~spl2_1),
% 0.21/0.59    inference(avatar_split_clause,[],[f82,f58,f116])).
% 0.21/0.59  fof(f82,plain,(
% 0.21/0.59    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~spl2_1),
% 0.21/0.59    inference(resolution,[],[f60,f43])).
% 0.21/0.59  fof(f112,plain,(
% 0.21/0.59    spl2_8),
% 0.21/0.59    inference(avatar_split_clause,[],[f36,f109])).
% 0.21/0.59  fof(f36,plain,(
% 0.21/0.59    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 0.21/0.59    inference(cnf_transformation,[],[f15])).
% 0.21/0.59  fof(f15,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.59    inference(flattening,[],[f14])).
% 0.21/0.59  fof(f14,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f13])).
% 0.21/0.59  fof(f13,negated_conjecture,(
% 0.21/0.59    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.59    inference(negated_conjecture,[],[f12])).
% 0.21/0.59  fof(f12,conjecture,(
% 0.21/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 0.21/0.59  fof(f107,plain,(
% 0.21/0.59    spl2_7),
% 0.21/0.59    inference(avatar_split_clause,[],[f35,f104])).
% 0.21/0.59  fof(f35,plain,(
% 0.21/0.59    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f15])).
% 0.21/0.59  fof(f102,plain,(
% 0.21/0.59    ~spl2_6),
% 0.21/0.59    inference(avatar_split_clause,[],[f37,f99])).
% 0.21/0.59  fof(f37,plain,(
% 0.21/0.59    sK1 != k2_funct_1(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f15])).
% 0.21/0.59  fof(f81,plain,(
% 0.21/0.59    spl2_5),
% 0.21/0.59    inference(avatar_split_clause,[],[f39,f78])).
% 0.21/0.59  fof(f39,plain,(
% 0.21/0.59    v1_funct_1(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f15])).
% 0.21/0.59  fof(f76,plain,(
% 0.21/0.59    spl2_4),
% 0.21/0.59    inference(avatar_split_clause,[],[f38,f73])).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    v1_relat_1(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f15])).
% 0.21/0.59  fof(f71,plain,(
% 0.21/0.60    spl2_3),
% 0.21/0.60    inference(avatar_split_clause,[],[f34,f68])).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    v2_funct_1(sK0)),
% 0.21/0.60    inference(cnf_transformation,[],[f15])).
% 0.21/0.60  fof(f66,plain,(
% 0.21/0.60    spl2_2),
% 0.21/0.60    inference(avatar_split_clause,[],[f33,f63])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    v1_funct_1(sK1)),
% 0.21/0.60    inference(cnf_transformation,[],[f15])).
% 0.21/0.60  fof(f61,plain,(
% 0.21/0.60    spl2_1),
% 0.21/0.60    inference(avatar_split_clause,[],[f32,f58])).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    v1_relat_1(sK1)),
% 0.21/0.60    inference(cnf_transformation,[],[f15])).
% 0.21/0.60  % SZS output end Proof for theBenchmark
% 0.21/0.60  % (28472)------------------------------
% 0.21/0.60  % (28472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (28472)Termination reason: Refutation
% 0.21/0.60  
% 0.21/0.60  % (28472)Memory used [KB]: 11769
% 0.21/0.60  % (28472)Time elapsed: 0.156 s
% 0.21/0.60  % (28472)------------------------------
% 0.21/0.60  % (28472)------------------------------
% 0.21/0.60  % (28468)Success in time 0.24 s
%------------------------------------------------------------------------------
