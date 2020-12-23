%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:07 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 317 expanded)
%              Number of leaves         :   42 ( 135 expanded)
%              Depth                    :   11
%              Number of atoms          :  697 (1301 expanded)
%              Number of equality atoms :  114 ( 232 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f89,f93,f97,f101,f105,f113,f740,f756,f768,f798,f851,f870,f964,f995,f1025,f1050,f1141,f1183,f1190,f1198,f1214,f1218,f1219,f1221])).

fof(f1221,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK1)) != k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))
    | r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)))
    | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1219,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK0)) != k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | v1_relat_1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1218,plain,
    ( ~ spl6_6
    | spl6_52 ),
    inference(avatar_split_clause,[],[f1216,f987,f103])).

fof(f103,plain,
    ( spl6_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f987,plain,
    ( spl6_52
  <=> v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f1216,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_52 ),
    inference(resolution,[],[f988,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f988,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | spl6_52 ),
    inference(avatar_component_clause,[],[f987])).

fof(f1214,plain,
    ( ~ spl6_6
    | ~ spl6_5
    | spl6_47 ),
    inference(avatar_split_clause,[],[f1211,f967,f99,f103])).

fof(f99,plain,
    ( spl6_5
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f967,plain,
    ( spl6_47
  <=> v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f1211,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl6_47 ),
    inference(resolution,[],[f968,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_wellord1)).

fof(f968,plain,
    ( ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | spl6_47 ),
    inference(avatar_component_clause,[],[f967])).

fof(f1198,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK0)) != k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | r4_wellord1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1190,plain,
    ( spl6_54
    | ~ spl6_3
    | spl6_2
    | ~ spl6_4
    | ~ spl6_24
    | spl6_33 ),
    inference(avatar_split_clause,[],[f1187,f846,f766,f95,f87,f91,f993])).

fof(f993,plain,
    ( spl6_54
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f91,plain,
    ( spl6_3
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f87,plain,
    ( spl6_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f95,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f766,plain,
    ( spl6_24
  <=> ! [X1,X0] :
        ( r2_hidden(X0,k1_wellord1(sK2,X1))
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | X0 = X1
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f846,plain,
    ( spl6_33
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f1187,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl6_4
    | ~ spl6_24
    | spl6_33 ),
    inference(resolution,[],[f1163,f774])).

fof(f774,plain,
    ( ! [X1] :
        ( r2_hidden(sK0,k1_wellord1(sK2,X1))
        | sK0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(X1,k1_wellord1(sK2,sK0)) )
    | ~ spl6_4
    | ~ spl6_24 ),
    inference(resolution,[],[f767,f96])).

fof(f96,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f767,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | X0 = X1
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(X0,k1_wellord1(sK2,X1)) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f766])).

fof(f1163,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | spl6_33 ),
    inference(avatar_component_clause,[],[f846])).

fof(f1183,plain,
    ( ~ spl6_75
    | ~ spl6_35
    | ~ spl6_36
    | ~ spl6_80
    | ~ spl6_33
    | ~ spl6_7
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f1179,f868,f110,f846,f1181,f861,f858,f1155])).

fof(f1155,plain,
    ( spl6_75
  <=> v1_relat_1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f858,plain,
    ( spl6_35
  <=> v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f861,plain,
    ( spl6_36
  <=> v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f1181,plain,
    ( spl6_80
  <=> r4_wellord1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f110,plain,
    ( spl6_7
  <=> ! [X0] : k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f868,plain,
    ( spl6_38
  <=> k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f1179,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ r4_wellord1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ v1_relat_1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)))
    | ~ spl6_7
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f1111,f111])).

fof(f111,plain,
    ( ! [X0] : k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f1111,plain,
    ( ~ r4_wellord1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))))
    | ~ v1_relat_1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)))
    | ~ spl6_38 ),
    inference(superposition,[],[f166,f869])).

fof(f869,plain,
    ( k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f868])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X0)),X1)
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k3_relat_1(X1))
      | ~ v1_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1)
      | ~ r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X0)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ),
    inference(resolution,[],[f52,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f1141,plain,
    ( spl6_65
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f1140,f868,f110,f103,f1115])).

fof(f1115,plain,
    ( spl6_65
  <=> k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f1140,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f1098,f111])).

fof(f1098,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))),k1_wellord1(sK2,sK0))
    | ~ spl6_6
    | ~ spl6_38 ),
    inference(superposition,[],[f175,f869])).

fof(f175,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,k3_relat_1(k2_wellord1(sK2,X0))),k1_wellord1(k2_wellord1(sK2,X0),X1)) = k2_wellord1(sK2,k1_wellord1(k2_wellord1(sK2,X0),X1))
    | ~ spl6_6 ),
    inference(resolution,[],[f122,f104])).

fof(f104,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f122,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_relat_1(X1)
        | k2_wellord1(k2_wellord1(sK2,k3_relat_1(k2_wellord1(X1,X2))),k1_wellord1(k2_wellord1(X1,X2),X3)) = k2_wellord1(sK2,k1_wellord1(k2_wellord1(X1,X2),X3)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f119,f72])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k2_wellord1(k2_wellord1(sK2,k3_relat_1(X0)),k1_wellord1(X0,X1)) = k2_wellord1(sK2,k1_wellord1(X0,X1)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f117,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_wellord1(k2_wellord1(sK2,X1),X0) = k2_wellord1(sK2,X0) )
    | ~ spl6_6 ),
    inference(resolution,[],[f76,f104])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

fof(f1050,plain,
    ( ~ spl6_6
    | spl6_35 ),
    inference(avatar_split_clause,[],[f1048,f858,f103])).

fof(f1048,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_35 ),
    inference(resolution,[],[f859,f72])).

fof(f859,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | spl6_35 ),
    inference(avatar_component_clause,[],[f858])).

fof(f1025,plain,
    ( ~ spl6_6
    | ~ spl6_5
    | spl6_36 ),
    inference(avatar_split_clause,[],[f1022,f861,f99,f103])).

fof(f1022,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl6_36 ),
    inference(resolution,[],[f862,f74])).

fof(f862,plain,
    ( ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | spl6_36 ),
    inference(avatar_component_clause,[],[f861])).

fof(f995,plain,
    ( ~ spl6_52
    | ~ spl6_47
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_7
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f985,f849,f110,f993,f990,f967,f987])).

fof(f990,plain,
    ( spl6_53
  <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f849,plain,
    ( spl6_34
  <=> k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f985,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ spl6_7
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f929,f111])).

fof(f929,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)))
    | ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ spl6_34 ),
    inference(superposition,[],[f52,f850])).

fof(f850,plain,
    ( k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f849])).

fof(f964,plain,
    ( spl6_40
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f963,f849,f110,f103,f938])).

fof(f938,plain,
    ( spl6_40
  <=> k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f963,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f921,f111])).

fof(f921,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))),k1_wellord1(sK2,sK1))
    | ~ spl6_6
    | ~ spl6_34 ),
    inference(superposition,[],[f175,f850])).

fof(f870,plain,
    ( ~ spl6_6
    | ~ spl6_5
    | spl6_38
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f855,f846,f868,f99,f103])).

fof(f855,plain,
    ( k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_33 ),
    inference(resolution,[],[f847,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X0,k1_wellord1(X2,X1))
          & v2_wellord1(X2) )
       => k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_wellord1)).

fof(f847,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f846])).

fof(f851,plain,
    ( spl6_2
    | spl6_33
    | spl6_34
    | ~ spl6_4
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f840,f796,f95,f849,f846,f87])).

fof(f796,plain,
    ( spl6_29
  <=> ! [X1] :
        ( sK1 = X1
        | k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),sK1)
        | r2_hidden(X1,k1_wellord1(sK2,sK1))
        | ~ r2_hidden(X1,k3_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f840,plain,
    ( k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1)
    | r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | sK0 = sK1
    | ~ spl6_4
    | ~ spl6_29 ),
    inference(resolution,[],[f797,f96])).

fof(f797,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),sK1)
        | r2_hidden(X1,k1_wellord1(sK2,sK1))
        | sK1 = X1 )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f796])).

fof(f798,plain,
    ( ~ spl6_6
    | ~ spl6_5
    | spl6_29
    | ~ spl6_3
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f792,f766,f91,f796,f99,f103])).

fof(f792,plain,
    ( ! [X1] :
        ( sK1 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(X1,k1_wellord1(sK2,sK1))
        | k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),sK1)
        | ~ v2_wellord1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_3
    | ~ spl6_24 ),
    inference(resolution,[],[f773,f77])).

fof(f773,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_wellord1(sK2,X0))
        | sK1 = X0
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(X0,k1_wellord1(sK2,sK1)) )
    | ~ spl6_3
    | ~ spl6_24 ),
    inference(resolution,[],[f767,f92])).

fof(f92,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f768,plain,
    ( ~ spl6_6
    | spl6_24
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f764,f754,f766,f103])).

fof(f754,plain,
    ( spl6_22
  <=> ! [X1,X0] :
        ( X0 = X1
        | r2_hidden(X0,k1_wellord1(sK2,X1))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f764,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_wellord1(sK2,X1))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | X0 = X1
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | ~ v1_relat_1(sK2) )
    | ~ spl6_22 ),
    inference(duplicate_literal_removal,[],[f761])).

fof(f761,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_wellord1(sK2,X1))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | X0 = X1
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | X0 = X1
        | ~ v1_relat_1(sK2) )
    | ~ spl6_22 ),
    inference(resolution,[],[f755,f78])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X1),X0)
      | r2_hidden(X4,k1_wellord1(X0,X1))
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
                | sK5(X0,X1,X2) = X1
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
                  & sK5(X0,X1,X2) != X1 )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
          | sK5(X0,X1,X2) = X1
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
            & sK5(X0,X1,X2) != X1 )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f755,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X1,X0),sK2)
        | r2_hidden(X0,k1_wellord1(sK2,X1))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | X0 = X1 )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f754])).

fof(f756,plain,
    ( ~ spl6_6
    | spl6_22
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f752,f738,f754,f103])).

fof(f738,plain,
    ( spl6_21
  <=> ! [X1,X0] :
        ( X0 = X1
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f752,plain,
    ( ! [X0,X1] :
        ( X0 = X1
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(X0,k1_wellord1(sK2,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl6_21 ),
    inference(duplicate_literal_removal,[],[f747])).

fof(f747,plain,
    ( ! [X0,X1] :
        ( X0 = X1
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(X0,k1_wellord1(sK2,X1))
        | X0 = X1
        | ~ v1_relat_1(sK2) )
    | ~ spl6_21 ),
    inference(resolution,[],[f739,f78])).

fof(f739,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2)) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f738])).

fof(f740,plain,
    ( ~ spl6_5
    | spl6_21
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f731,f103,f738,f99])).

fof(f731,plain,
    ( ! [X0,X1] :
        ( X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ v2_wellord1(sK2) )
    | ~ spl6_6 ),
    inference(resolution,[],[f361,f104])).

fof(f361,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_relat_1(X8)
      | X6 = X7
      | ~ r2_hidden(X7,k3_relat_1(X8))
      | ~ r2_hidden(X6,k3_relat_1(X8))
      | r2_hidden(k4_tarski(X7,X6),X8)
      | r2_hidden(k4_tarski(X6,X7),X8)
      | ~ v2_wellord1(X8) ) ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(k4_tarski(X6,X7),X8)
      | X6 = X7
      | ~ r2_hidden(X7,k3_relat_1(X8))
      | ~ r2_hidden(X6,k3_relat_1(X8))
      | r2_hidden(k4_tarski(X7,X6),X8)
      | ~ v1_relat_1(X8)
      | ~ v2_wellord1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(resolution,[],[f53,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f53,plain,(
    ! [X4,X0,X3] :
      ( ~ v6_relat_2(X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | r2_hidden(k4_tarski(X4,X3),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
            & sK3(X0) != sK4(X0)
            & r2_hidden(sK4(X0),k3_relat_1(X0))
            & r2_hidden(sK3(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
        & sK3(X0) != sK4(X0)
        & r2_hidden(sK4(X0),k3_relat_1(X0))
        & r2_hidden(sK3(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(f113,plain,
    ( spl6_7
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f107,f103,f99,f110])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ v2_wellord1(sK2)
        | k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0))) )
    | ~ spl6_6 ),
    inference(resolution,[],[f75,f104])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v2_wellord1(X1)
      | k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).

fof(f105,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f46,f103])).

fof(f46,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    & sK0 != sK1
    & r2_hidden(sK1,k3_relat_1(sK2))
    & r2_hidden(sK0,k3_relat_1(sK2))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
        & X0 != X1
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
      & sK0 != sK1
      & r2_hidden(sK1,k3_relat_1(sK2))
      & r2_hidden(sK0,k3_relat_1(sK2))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
      & X0 != X1
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
      & X0 != X1
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ~ ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
            & X0 != X1
            & r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
          & X0 != X1
          & r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_wellord1)).

fof(f101,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f47,f99])).

fof(f47,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f97,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f48,f95])).

fof(f48,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f49,f91])).

fof(f49,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f50,f87])).

fof(f50,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f51,f83])).

fof(f83,plain,
    ( spl6_1
  <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f51,plain,(
    r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:24:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (24248)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (24250)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (24246)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (24262)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (24247)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (24249)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (24257)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (24260)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (24251)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (24252)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (24244)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (24258)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (24259)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (24263)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (24245)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (24255)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (24245)Refutation not found, incomplete strategy% (24245)------------------------------
% 0.20/0.50  % (24245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (24245)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (24245)Memory used [KB]: 10618
% 0.20/0.50  % (24245)Time elapsed: 0.091 s
% 0.20/0.50  % (24245)------------------------------
% 0.20/0.50  % (24245)------------------------------
% 0.20/0.50  % (24264)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (24253)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (24254)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (24265)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.52  % (24261)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.53  % (24265)Refutation not found, incomplete strategy% (24265)------------------------------
% 0.20/0.53  % (24265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24265)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24265)Memory used [KB]: 10618
% 0.20/0.53  % (24265)Time elapsed: 0.125 s
% 0.20/0.53  % (24265)------------------------------
% 0.20/0.53  % (24265)------------------------------
% 1.54/0.56  % (24250)Refutation found. Thanks to Tanya!
% 1.54/0.56  % SZS status Theorem for theBenchmark
% 1.54/0.56  % SZS output start Proof for theBenchmark
% 1.54/0.56  fof(f1222,plain,(
% 1.54/0.56    $false),
% 1.54/0.56    inference(avatar_sat_refutation,[],[f85,f89,f93,f97,f101,f105,f113,f740,f756,f768,f798,f851,f870,f964,f995,f1025,f1050,f1141,f1183,f1190,f1198,f1214,f1218,f1219,f1221])).
% 1.54/0.56  fof(f1221,plain,(
% 1.54/0.56    k2_wellord1(sK2,k1_wellord1(sK2,sK1)) != k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)) | r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))) | ~r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))),
% 1.54/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.56  fof(f1219,plain,(
% 1.54/0.56    k2_wellord1(sK2,k1_wellord1(sK2,sK0)) != k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) | v1_relat_1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))) | ~v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))),
% 1.54/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.56  fof(f1218,plain,(
% 1.54/0.56    ~spl6_6 | spl6_52),
% 1.54/0.56    inference(avatar_split_clause,[],[f1216,f987,f103])).
% 1.54/0.56  fof(f103,plain,(
% 1.54/0.56    spl6_6 <=> v1_relat_1(sK2)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.54/0.56  fof(f987,plain,(
% 1.54/0.56    spl6_52 <=> v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 1.54/0.56  fof(f1216,plain,(
% 1.54/0.56    ~v1_relat_1(sK2) | spl6_52),
% 1.54/0.56    inference(resolution,[],[f988,f72])).
% 1.54/0.56  fof(f72,plain,(
% 1.54/0.56    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f23])).
% 1.54/0.56  fof(f23,plain,(
% 1.54/0.56    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f3])).
% 1.54/0.56  fof(f3,axiom,(
% 1.54/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 1.54/0.56  fof(f988,plain,(
% 1.54/0.56    ~v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) | spl6_52),
% 1.54/0.56    inference(avatar_component_clause,[],[f987])).
% 1.54/0.56  fof(f1214,plain,(
% 1.54/0.56    ~spl6_6 | ~spl6_5 | spl6_47),
% 1.54/0.56    inference(avatar_split_clause,[],[f1211,f967,f99,f103])).
% 1.54/0.56  fof(f99,plain,(
% 1.54/0.56    spl6_5 <=> v2_wellord1(sK2)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.54/0.56  fof(f967,plain,(
% 1.54/0.56    spl6_47 <=> v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 1.54/0.56  fof(f1211,plain,(
% 1.54/0.56    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl6_47),
% 1.54/0.56    inference(resolution,[],[f968,f74])).
% 1.54/0.56  fof(f74,plain,(
% 1.54/0.56    ( ! [X0,X1] : (v2_wellord1(k2_wellord1(X1,X0)) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f26])).
% 1.54/0.56  fof(f26,plain,(
% 1.54/0.56    ! [X0,X1] : (v2_wellord1(k2_wellord1(X1,X0)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 1.54/0.56    inference(flattening,[],[f25])).
% 1.54/0.56  fof(f25,plain,(
% 1.54/0.56    ! [X0,X1] : ((v2_wellord1(k2_wellord1(X1,X0)) | ~v2_wellord1(X1)) | ~v1_relat_1(X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f7])).
% 1.54/0.56  fof(f7,axiom,(
% 1.54/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => v2_wellord1(k2_wellord1(X1,X0))))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_wellord1)).
% 1.54/0.56  fof(f968,plain,(
% 1.54/0.56    ~v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) | spl6_47),
% 1.54/0.56    inference(avatar_component_clause,[],[f967])).
% 1.54/0.56  fof(f1198,plain,(
% 1.54/0.56    k2_wellord1(sK2,k1_wellord1(sK2,sK0)) != k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) | r4_wellord1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) | ~r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))),
% 1.54/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.56  fof(f1190,plain,(
% 1.54/0.56    spl6_54 | ~spl6_3 | spl6_2 | ~spl6_4 | ~spl6_24 | spl6_33),
% 1.54/0.56    inference(avatar_split_clause,[],[f1187,f846,f766,f95,f87,f91,f993])).
% 1.54/0.56  fof(f993,plain,(
% 1.54/0.56    spl6_54 <=> r2_hidden(sK1,k1_wellord1(sK2,sK0))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 1.54/0.56  fof(f91,plain,(
% 1.54/0.56    spl6_3 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.54/0.56  fof(f87,plain,(
% 1.54/0.56    spl6_2 <=> sK0 = sK1),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.54/0.56  fof(f95,plain,(
% 1.54/0.56    spl6_4 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.54/0.56  fof(f766,plain,(
% 1.54/0.56    spl6_24 <=> ! [X1,X0] : (r2_hidden(X0,k1_wellord1(sK2,X1)) | r2_hidden(X1,k1_wellord1(sK2,X0)) | X0 = X1 | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.54/0.56  fof(f846,plain,(
% 1.54/0.56    spl6_33 <=> r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.54/0.56  fof(f1187,plain,(
% 1.54/0.56    sK0 = sK1 | ~r2_hidden(sK1,k3_relat_1(sK2)) | r2_hidden(sK1,k1_wellord1(sK2,sK0)) | (~spl6_4 | ~spl6_24 | spl6_33)),
% 1.54/0.56    inference(resolution,[],[f1163,f774])).
% 1.54/0.56  fof(f774,plain,(
% 1.54/0.56    ( ! [X1] : (r2_hidden(sK0,k1_wellord1(sK2,X1)) | sK0 = X1 | ~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(X1,k1_wellord1(sK2,sK0))) ) | (~spl6_4 | ~spl6_24)),
% 1.54/0.56    inference(resolution,[],[f767,f96])).
% 1.54/0.56  fof(f96,plain,(
% 1.54/0.56    r2_hidden(sK0,k3_relat_1(sK2)) | ~spl6_4),
% 1.54/0.56    inference(avatar_component_clause,[],[f95])).
% 1.54/0.56  fof(f767,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(X1,k1_wellord1(sK2,X0)) | X0 = X1 | ~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(X0,k1_wellord1(sK2,X1))) ) | ~spl6_24),
% 1.54/0.56    inference(avatar_component_clause,[],[f766])).
% 1.54/0.56  fof(f1163,plain,(
% 1.54/0.56    ~r2_hidden(sK0,k1_wellord1(sK2,sK1)) | spl6_33),
% 1.54/0.56    inference(avatar_component_clause,[],[f846])).
% 1.54/0.56  fof(f1183,plain,(
% 1.54/0.56    ~spl6_75 | ~spl6_35 | ~spl6_36 | ~spl6_80 | ~spl6_33 | ~spl6_7 | ~spl6_38),
% 1.54/0.56    inference(avatar_split_clause,[],[f1179,f868,f110,f846,f1181,f861,f858,f1155])).
% 1.54/0.56  fof(f1155,plain,(
% 1.54/0.56    spl6_75 <=> v1_relat_1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).
% 1.54/0.56  fof(f858,plain,(
% 1.54/0.56    spl6_35 <=> v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 1.54/0.56  fof(f861,plain,(
% 1.54/0.56    spl6_36 <=> v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 1.54/0.56  fof(f1181,plain,(
% 1.54/0.56    spl6_80 <=> r4_wellord1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).
% 1.54/0.56  fof(f110,plain,(
% 1.54/0.56    spl6_7 <=> ! [X0] : k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.54/0.56  fof(f868,plain,(
% 1.54/0.56    spl6_38 <=> k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 1.54/0.56  fof(f1179,plain,(
% 1.54/0.56    ~r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~r4_wellord1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) | ~v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) | ~v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) | ~v1_relat_1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))) | (~spl6_7 | ~spl6_38)),
% 1.54/0.56    inference(forward_demodulation,[],[f1111,f111])).
% 1.54/0.56  fof(f111,plain,(
% 1.54/0.56    ( ! [X0] : (k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0)))) ) | ~spl6_7),
% 1.54/0.56    inference(avatar_component_clause,[],[f110])).
% 1.54/0.56  fof(f1111,plain,(
% 1.54/0.56    ~r4_wellord1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) | ~v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) | ~v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) | ~r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))) | ~v1_relat_1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))) | ~spl6_38),
% 1.54/0.56    inference(superposition,[],[f166,f869])).
% 1.68/0.57  fof(f869,plain,(
% 1.68/0.57    k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0) | ~spl6_38),
% 1.68/0.57    inference(avatar_component_clause,[],[f868])).
% 1.68/0.57  fof(f166,plain,(
% 1.68/0.57    ( ! [X0,X1] : (~r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X0)),X1) | ~v2_wellord1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k3_relat_1(X1)) | ~v1_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))) )),
% 1.68/0.57    inference(duplicate_literal_removal,[],[f165])).
% 1.68/0.57  fof(f165,plain,(
% 1.68/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1) | ~r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X0)),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))) )),
% 1.68/0.57    inference(resolution,[],[f52,f65])).
% 1.68/0.57  fof(f65,plain,(
% 1.68/0.57    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.68/0.57    inference(cnf_transformation,[],[f21])).
% 1.68/0.57  fof(f21,plain,(
% 1.68/0.57    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(flattening,[],[f20])).
% 1.68/0.57  fof(f20,plain,(
% 1.68/0.57    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(ennf_transformation,[],[f10])).
% 1.68/0.57  fof(f10,axiom,(
% 1.68/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 1.68/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 1.68/0.57  fof(f52,plain,(
% 1.68/0.57    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.57    inference(cnf_transformation,[],[f17])).
% 1.68/0.57  fof(f17,plain,(
% 1.68/0.57    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(flattening,[],[f16])).
% 1.68/0.57  fof(f16,plain,(
% 1.68/0.57    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(ennf_transformation,[],[f11])).
% 1.68/0.57  fof(f11,axiom,(
% 1.68/0.57    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 1.68/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 1.68/0.57  fof(f1141,plain,(
% 1.68/0.57    spl6_65 | ~spl6_6 | ~spl6_7 | ~spl6_38),
% 1.68/0.57    inference(avatar_split_clause,[],[f1140,f868,f110,f103,f1115])).
% 1.68/0.57  fof(f1115,plain,(
% 1.68/0.57    spl6_65 <=> k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))),
% 1.68/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 1.68/0.57  fof(f1140,plain,(
% 1.68/0.57    k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) | (~spl6_6 | ~spl6_7 | ~spl6_38)),
% 1.68/0.57    inference(forward_demodulation,[],[f1098,f111])).
% 1.68/0.57  fof(f1098,plain,(
% 1.68/0.57    k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))),k1_wellord1(sK2,sK0)) | (~spl6_6 | ~spl6_38)),
% 1.68/0.57    inference(superposition,[],[f175,f869])).
% 1.68/0.57  fof(f175,plain,(
% 1.68/0.57    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,k3_relat_1(k2_wellord1(sK2,X0))),k1_wellord1(k2_wellord1(sK2,X0),X1)) = k2_wellord1(sK2,k1_wellord1(k2_wellord1(sK2,X0),X1))) ) | ~spl6_6),
% 1.68/0.57    inference(resolution,[],[f122,f104])).
% 1.68/0.57  fof(f104,plain,(
% 1.68/0.57    v1_relat_1(sK2) | ~spl6_6),
% 1.68/0.57    inference(avatar_component_clause,[],[f103])).
% 1.68/0.57  fof(f122,plain,(
% 1.68/0.57    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k2_wellord1(k2_wellord1(sK2,k3_relat_1(k2_wellord1(X1,X2))),k1_wellord1(k2_wellord1(X1,X2),X3)) = k2_wellord1(sK2,k1_wellord1(k2_wellord1(X1,X2),X3))) ) | ~spl6_6),
% 1.68/0.57    inference(resolution,[],[f119,f72])).
% 1.68/0.57  fof(f119,plain,(
% 1.68/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_wellord1(k2_wellord1(sK2,k3_relat_1(X0)),k1_wellord1(X0,X1)) = k2_wellord1(sK2,k1_wellord1(X0,X1))) ) | ~spl6_6),
% 1.68/0.57    inference(resolution,[],[f117,f73])).
% 1.68/0.57  fof(f73,plain,(
% 1.68/0.57    ( ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.68/0.57    inference(cnf_transformation,[],[f24])).
% 1.68/0.57  fof(f24,plain,(
% 1.68/0.57    ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.68/0.57    inference(ennf_transformation,[],[f5])).
% 1.68/0.57  fof(f5,axiom,(
% 1.68/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)))),
% 1.68/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).
% 1.68/0.57  fof(f117,plain,(
% 1.68/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_wellord1(k2_wellord1(sK2,X1),X0) = k2_wellord1(sK2,X0)) ) | ~spl6_6),
% 1.68/0.57    inference(resolution,[],[f76,f104])).
% 1.68/0.57  fof(f76,plain,(
% 1.68/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0)) )),
% 1.68/0.57    inference(cnf_transformation,[],[f30])).
% 1.68/0.57  fof(f30,plain,(
% 1.68/0.57    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.68/0.57    inference(flattening,[],[f29])).
% 1.68/0.57  fof(f29,plain,(
% 1.68/0.57    ! [X0,X1,X2] : ((k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.68/0.57    inference(ennf_transformation,[],[f6])).
% 1.68/0.57  fof(f6,axiom,(
% 1.68/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0)))),
% 1.68/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).
% 1.68/0.57  fof(f1050,plain,(
% 1.68/0.57    ~spl6_6 | spl6_35),
% 1.68/0.57    inference(avatar_split_clause,[],[f1048,f858,f103])).
% 1.68/0.57  fof(f1048,plain,(
% 1.68/0.57    ~v1_relat_1(sK2) | spl6_35),
% 1.68/0.57    inference(resolution,[],[f859,f72])).
% 1.68/0.57  fof(f859,plain,(
% 1.68/0.57    ~v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) | spl6_35),
% 1.68/0.57    inference(avatar_component_clause,[],[f858])).
% 1.68/0.57  fof(f1025,plain,(
% 1.68/0.57    ~spl6_6 | ~spl6_5 | spl6_36),
% 1.68/0.57    inference(avatar_split_clause,[],[f1022,f861,f99,f103])).
% 1.68/0.57  fof(f1022,plain,(
% 1.68/0.57    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl6_36),
% 1.68/0.57    inference(resolution,[],[f862,f74])).
% 1.68/0.57  fof(f862,plain,(
% 1.68/0.57    ~v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) | spl6_36),
% 1.68/0.57    inference(avatar_component_clause,[],[f861])).
% 1.68/0.57  fof(f995,plain,(
% 1.68/0.57    ~spl6_52 | ~spl6_47 | ~spl6_53 | ~spl6_54 | ~spl6_7 | ~spl6_34),
% 1.68/0.57    inference(avatar_split_clause,[],[f985,f849,f110,f993,f990,f967,f987])).
% 1.68/0.57  fof(f990,plain,(
% 1.68/0.57    spl6_53 <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)))),
% 1.68/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 1.68/0.57  fof(f849,plain,(
% 1.68/0.57    spl6_34 <=> k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1)),
% 1.68/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.68/0.57  fof(f985,plain,(
% 1.68/0.57    ~r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))) | ~v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) | ~v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) | (~spl6_7 | ~spl6_34)),
% 1.68/0.57    inference(forward_demodulation,[],[f929,f111])).
% 1.68/0.57  fof(f929,plain,(
% 1.68/0.57    ~r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))) | ~r2_hidden(sK1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))) | ~v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) | ~v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) | ~spl6_34),
% 1.68/0.57    inference(superposition,[],[f52,f850])).
% 1.68/0.57  fof(f850,plain,(
% 1.68/0.57    k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1) | ~spl6_34),
% 1.68/0.57    inference(avatar_component_clause,[],[f849])).
% 1.68/0.57  fof(f964,plain,(
% 1.68/0.57    spl6_40 | ~spl6_6 | ~spl6_7 | ~spl6_34),
% 1.68/0.57    inference(avatar_split_clause,[],[f963,f849,f110,f103,f938])).
% 1.68/0.57  fof(f938,plain,(
% 1.68/0.57    spl6_40 <=> k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))),
% 1.68/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 1.68/0.57  fof(f963,plain,(
% 1.68/0.57    k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)) | (~spl6_6 | ~spl6_7 | ~spl6_34)),
% 1.68/0.57    inference(forward_demodulation,[],[f921,f111])).
% 1.68/0.57  fof(f921,plain,(
% 1.68/0.57    k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))),k1_wellord1(sK2,sK1)) | (~spl6_6 | ~spl6_34)),
% 1.68/0.57    inference(superposition,[],[f175,f850])).
% 1.68/0.57  fof(f870,plain,(
% 1.68/0.57    ~spl6_6 | ~spl6_5 | spl6_38 | ~spl6_33),
% 1.68/0.57    inference(avatar_split_clause,[],[f855,f846,f868,f99,f103])).
% 1.68/0.57  fof(f855,plain,(
% 1.68/0.57    k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0) | ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | ~spl6_33),
% 1.68/0.57    inference(resolution,[],[f847,f77])).
% 1.68/0.57  fof(f77,plain,(
% 1.68/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_wellord1(X2,X1)) | k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 1.68/0.57    inference(cnf_transformation,[],[f32])).
% 1.68/0.57  fof(f32,plain,(
% 1.68/0.57    ! [X0,X1,X2] : (k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) | ~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 1.68/0.57    inference(flattening,[],[f31])).
% 1.68/0.57  fof(f31,plain,(
% 1.68/0.57    ! [X0,X1,X2] : ((k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) | (~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 1.68/0.57    inference(ennf_transformation,[],[f8])).
% 1.68/0.57  fof(f8,axiom,(
% 1.68/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X0,k1_wellord1(X2,X1)) & v2_wellord1(X2)) => k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)))),
% 1.68/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_wellord1)).
% 1.68/0.57  fof(f847,plain,(
% 1.68/0.57    r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~spl6_33),
% 1.68/0.57    inference(avatar_component_clause,[],[f846])).
% 1.68/0.57  fof(f851,plain,(
% 1.68/0.57    spl6_2 | spl6_33 | spl6_34 | ~spl6_4 | ~spl6_29),
% 1.68/0.57    inference(avatar_split_clause,[],[f840,f796,f95,f849,f846,f87])).
% 1.68/0.57  fof(f796,plain,(
% 1.68/0.57    spl6_29 <=> ! [X1] : (sK1 = X1 | k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),sK1) | r2_hidden(X1,k1_wellord1(sK2,sK1)) | ~r2_hidden(X1,k3_relat_1(sK2)))),
% 1.68/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 1.68/0.57  fof(f840,plain,(
% 1.68/0.57    k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1) | r2_hidden(sK0,k1_wellord1(sK2,sK1)) | sK0 = sK1 | (~spl6_4 | ~spl6_29)),
% 1.68/0.57    inference(resolution,[],[f797,f96])).
% 1.68/0.57  fof(f797,plain,(
% 1.68/0.57    ( ! [X1] : (~r2_hidden(X1,k3_relat_1(sK2)) | k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),sK1) | r2_hidden(X1,k1_wellord1(sK2,sK1)) | sK1 = X1) ) | ~spl6_29),
% 1.68/0.57    inference(avatar_component_clause,[],[f796])).
% 1.68/0.57  fof(f798,plain,(
% 1.68/0.57    ~spl6_6 | ~spl6_5 | spl6_29 | ~spl6_3 | ~spl6_24),
% 1.68/0.57    inference(avatar_split_clause,[],[f792,f766,f91,f796,f99,f103])).
% 1.68/0.57  fof(f792,plain,(
% 1.68/0.57    ( ! [X1] : (sK1 = X1 | ~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(X1,k1_wellord1(sK2,sK1)) | k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),sK1) | ~v2_wellord1(sK2) | ~v1_relat_1(sK2)) ) | (~spl6_3 | ~spl6_24)),
% 1.68/0.57    inference(resolution,[],[f773,f77])).
% 1.68/0.57  fof(f773,plain,(
% 1.68/0.57    ( ! [X0] : (r2_hidden(sK1,k1_wellord1(sK2,X0)) | sK1 = X0 | ~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(X0,k1_wellord1(sK2,sK1))) ) | (~spl6_3 | ~spl6_24)),
% 1.68/0.57    inference(resolution,[],[f767,f92])).
% 1.68/0.57  fof(f92,plain,(
% 1.68/0.57    r2_hidden(sK1,k3_relat_1(sK2)) | ~spl6_3),
% 1.68/0.57    inference(avatar_component_clause,[],[f91])).
% 1.68/0.57  fof(f768,plain,(
% 1.68/0.57    ~spl6_6 | spl6_24 | ~spl6_22),
% 1.68/0.57    inference(avatar_split_clause,[],[f764,f754,f766,f103])).
% 1.68/0.57  fof(f754,plain,(
% 1.68/0.57    spl6_22 <=> ! [X1,X0] : (X0 = X1 | r2_hidden(X0,k1_wellord1(sK2,X1)) | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X1,X0),sK2))),
% 1.68/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.68/0.57  fof(f764,plain,(
% 1.68/0.57    ( ! [X0,X1] : (r2_hidden(X0,k1_wellord1(sK2,X1)) | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | X0 = X1 | r2_hidden(X1,k1_wellord1(sK2,X0)) | ~v1_relat_1(sK2)) ) | ~spl6_22),
% 1.68/0.57    inference(duplicate_literal_removal,[],[f761])).
% 1.68/0.57  fof(f761,plain,(
% 1.68/0.57    ( ! [X0,X1] : (r2_hidden(X0,k1_wellord1(sK2,X1)) | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | X0 = X1 | r2_hidden(X1,k1_wellord1(sK2,X0)) | X0 = X1 | ~v1_relat_1(sK2)) ) | ~spl6_22),
% 1.68/0.57    inference(resolution,[],[f755,f78])).
% 1.68/0.57  fof(f78,plain,(
% 1.68/0.57    ( ! [X4,X0,X1] : (~r2_hidden(k4_tarski(X4,X1),X0) | r2_hidden(X4,k1_wellord1(X0,X1)) | X1 = X4 | ~v1_relat_1(X0)) )),
% 1.68/0.57    inference(equality_resolution,[],[f68])).
% 1.68/0.57  fof(f68,plain,(
% 1.68/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.68/0.57    inference(cnf_transformation,[],[f45])).
% 1.68/0.57  fof(f45,plain,(
% 1.68/0.57    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0) | sK5(X0,X1,X2) = X1 | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0) & sK5(X0,X1,X2) != X1) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).
% 1.68/0.57  fof(f44,plain,(
% 1.68/0.57    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0) | sK5(X0,X1,X2) = X1 | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0) & sK5(X0,X1,X2) != X1) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.68/0.57    introduced(choice_axiom,[])).
% 1.68/0.57  fof(f43,plain,(
% 1.68/0.57    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(rectify,[],[f42])).
% 1.68/0.57  fof(f42,plain,(
% 1.68/0.57    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(flattening,[],[f41])).
% 1.68/0.57  fof(f41,plain,(
% 1.68/0.57    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(nnf_transformation,[],[f22])).
% 1.68/0.57  fof(f22,plain,(
% 1.68/0.57    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(ennf_transformation,[],[f1])).
% 1.68/0.57  fof(f1,axiom,(
% 1.68/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 1.68/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 1.68/0.57  fof(f755,plain,(
% 1.68/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),sK2) | r2_hidden(X0,k1_wellord1(sK2,X1)) | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | X0 = X1) ) | ~spl6_22),
% 1.68/0.57    inference(avatar_component_clause,[],[f754])).
% 1.68/0.57  fof(f756,plain,(
% 1.68/0.57    ~spl6_6 | spl6_22 | ~spl6_21),
% 1.68/0.57    inference(avatar_split_clause,[],[f752,f738,f754,f103])).
% 1.68/0.57  fof(f738,plain,(
% 1.68/0.57    spl6_21 <=> ! [X1,X0] : (X0 = X1 | r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)))),
% 1.68/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.68/0.57  fof(f752,plain,(
% 1.68/0.57    ( ! [X0,X1] : (X0 = X1 | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(X0,k1_wellord1(sK2,X1)) | ~v1_relat_1(sK2)) ) | ~spl6_21),
% 1.68/0.57    inference(duplicate_literal_removal,[],[f747])).
% 1.68/0.57  fof(f747,plain,(
% 1.68/0.57    ( ! [X0,X1] : (X0 = X1 | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(X0,k1_wellord1(sK2,X1)) | X0 = X1 | ~v1_relat_1(sK2)) ) | ~spl6_21),
% 1.68/0.57    inference(resolution,[],[f739,f78])).
% 1.68/0.57  fof(f739,plain,(
% 1.68/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2))) ) | ~spl6_21),
% 1.68/0.57    inference(avatar_component_clause,[],[f738])).
% 1.68/0.57  fof(f740,plain,(
% 1.68/0.57    ~spl6_5 | spl6_21 | ~spl6_6),
% 1.68/0.57    inference(avatar_split_clause,[],[f731,f103,f738,f99])).
% 1.68/0.57  fof(f731,plain,(
% 1.68/0.57    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X1,X0),sK2) | r2_hidden(k4_tarski(X0,X1),sK2) | ~v2_wellord1(sK2)) ) | ~spl6_6),
% 1.68/0.57    inference(resolution,[],[f361,f104])).
% 1.68/0.57  fof(f361,plain,(
% 1.68/0.57    ( ! [X6,X8,X7] : (~v1_relat_1(X8) | X6 = X7 | ~r2_hidden(X7,k3_relat_1(X8)) | ~r2_hidden(X6,k3_relat_1(X8)) | r2_hidden(k4_tarski(X7,X6),X8) | r2_hidden(k4_tarski(X6,X7),X8) | ~v2_wellord1(X8)) )),
% 1.68/0.57    inference(duplicate_literal_removal,[],[f358])).
% 1.68/0.57  fof(f358,plain,(
% 1.68/0.57    ( ! [X6,X8,X7] : (r2_hidden(k4_tarski(X6,X7),X8) | X6 = X7 | ~r2_hidden(X7,k3_relat_1(X8)) | ~r2_hidden(X6,k3_relat_1(X8)) | r2_hidden(k4_tarski(X7,X6),X8) | ~v1_relat_1(X8) | ~v2_wellord1(X8) | ~v1_relat_1(X8)) )),
% 1.68/0.57    inference(resolution,[],[f53,f62])).
% 1.68/0.57  fof(f62,plain,(
% 1.68/0.57    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.57    inference(cnf_transformation,[],[f40])).
% 1.68/0.57  fof(f40,plain,(
% 1.68/0.57    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(flattening,[],[f39])).
% 1.68/0.57  fof(f39,plain,(
% 1.68/0.57    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(nnf_transformation,[],[f19])).
% 1.68/0.57  fof(f19,plain,(
% 1.68/0.57    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(ennf_transformation,[],[f2])).
% 1.68/0.57  fof(f2,axiom,(
% 1.68/0.57    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 1.68/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).
% 1.68/0.57  fof(f53,plain,(
% 1.68/0.57    ( ! [X4,X0,X3] : (~v6_relat_2(X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | r2_hidden(k4_tarski(X4,X3),X0) | ~v1_relat_1(X0)) )),
% 1.68/0.57    inference(cnf_transformation,[],[f38])).
% 1.68/0.57  fof(f38,plain,(
% 1.68/0.57    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & ~r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) & sK3(X0) != sK4(X0) & r2_hidden(sK4(X0),k3_relat_1(X0)) & r2_hidden(sK3(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f37])).
% 1.68/0.57  fof(f37,plain,(
% 1.68/0.57    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & ~r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) & sK3(X0) != sK4(X0) & r2_hidden(sK4(X0),k3_relat_1(X0)) & r2_hidden(sK3(X0),k3_relat_1(X0))))),
% 1.68/0.57    introduced(choice_axiom,[])).
% 1.68/0.57  fof(f36,plain,(
% 1.68/0.57    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(rectify,[],[f35])).
% 1.68/0.57  fof(f35,plain,(
% 1.68/0.57    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(nnf_transformation,[],[f18])).
% 1.68/0.57  fof(f18,plain,(
% 1.68/0.57    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 1.68/0.57    inference(ennf_transformation,[],[f4])).
% 1.68/0.57  fof(f4,axiom,(
% 1.68/0.57    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 1.68/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).
% 1.68/0.57  fof(f113,plain,(
% 1.68/0.57    spl6_7 | ~spl6_5 | ~spl6_6),
% 1.68/0.57    inference(avatar_split_clause,[],[f107,f103,f99,f110])).
% 1.68/0.57  fof(f107,plain,(
% 1.68/0.57    ( ! [X0] : (~v2_wellord1(sK2) | k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0)))) ) | ~spl6_6),
% 1.68/0.57    inference(resolution,[],[f75,f104])).
% 1.68/0.57  fof(f75,plain,(
% 1.68/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v2_wellord1(X1) | k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))) )),
% 1.68/0.57    inference(cnf_transformation,[],[f28])).
% 1.68/0.57  fof(f28,plain,(
% 1.68/0.57    ! [X0,X1] : (k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 1.68/0.57    inference(flattening,[],[f27])).
% 1.68/0.57  fof(f27,plain,(
% 1.68/0.57    ! [X0,X1] : ((k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v2_wellord1(X1)) | ~v1_relat_1(X1))),
% 1.68/0.57    inference(ennf_transformation,[],[f9])).
% 1.68/0.57  fof(f9,axiom,(
% 1.68/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))))),
% 1.68/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).
% 1.68/0.57  fof(f105,plain,(
% 1.68/0.57    spl6_6),
% 1.68/0.57    inference(avatar_split_clause,[],[f46,f103])).
% 1.68/0.57  fof(f46,plain,(
% 1.68/0.57    v1_relat_1(sK2)),
% 1.68/0.57    inference(cnf_transformation,[],[f34])).
% 1.68/0.57  fof(f34,plain,(
% 1.68/0.57    r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) & sK0 != sK1 & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2)),
% 1.68/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f33])).
% 1.68/0.57  fof(f33,plain,(
% 1.68/0.57    ? [X0,X1,X2] : (r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1))) & X0 != X1 & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => (r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) & sK0 != sK1 & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2))),
% 1.68/0.57    introduced(choice_axiom,[])).
% 1.68/0.57  fof(f15,plain,(
% 1.68/0.57    ? [X0,X1,X2] : (r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1))) & X0 != X1 & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 1.68/0.57    inference(flattening,[],[f14])).
% 1.68/0.57  fof(f14,plain,(
% 1.68/0.57    ? [X0,X1,X2] : ((r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1))) & X0 != X1 & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) & v1_relat_1(X2))),
% 1.68/0.57    inference(ennf_transformation,[],[f13])).
% 1.68/0.57  fof(f13,negated_conjecture,(
% 1.68/0.57    ~! [X0,X1,X2] : (v1_relat_1(X2) => ~(r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1))) & X0 != X1 & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)))),
% 1.68/0.57    inference(negated_conjecture,[],[f12])).
% 1.68/0.57  fof(f12,conjecture,(
% 1.68/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ~(r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1))) & X0 != X1 & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)))),
% 1.68/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_wellord1)).
% 1.68/0.57  fof(f101,plain,(
% 1.68/0.57    spl6_5),
% 1.68/0.57    inference(avatar_split_clause,[],[f47,f99])).
% 1.68/0.57  fof(f47,plain,(
% 1.68/0.57    v2_wellord1(sK2)),
% 1.68/0.57    inference(cnf_transformation,[],[f34])).
% 1.68/0.57  fof(f97,plain,(
% 1.68/0.57    spl6_4),
% 1.68/0.57    inference(avatar_split_clause,[],[f48,f95])).
% 1.68/0.57  fof(f48,plain,(
% 1.68/0.57    r2_hidden(sK0,k3_relat_1(sK2))),
% 1.68/0.57    inference(cnf_transformation,[],[f34])).
% 1.68/0.57  fof(f93,plain,(
% 1.68/0.57    spl6_3),
% 1.68/0.57    inference(avatar_split_clause,[],[f49,f91])).
% 1.68/0.57  fof(f49,plain,(
% 1.68/0.57    r2_hidden(sK1,k3_relat_1(sK2))),
% 1.68/0.57    inference(cnf_transformation,[],[f34])).
% 1.68/0.57  fof(f89,plain,(
% 1.68/0.57    ~spl6_2),
% 1.68/0.57    inference(avatar_split_clause,[],[f50,f87])).
% 1.68/0.57  fof(f50,plain,(
% 1.68/0.57    sK0 != sK1),
% 1.68/0.57    inference(cnf_transformation,[],[f34])).
% 1.68/0.57  fof(f85,plain,(
% 1.68/0.57    spl6_1),
% 1.68/0.57    inference(avatar_split_clause,[],[f51,f83])).
% 1.68/0.57  fof(f83,plain,(
% 1.68/0.57    spl6_1 <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))),
% 1.68/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.68/0.57  fof(f51,plain,(
% 1.68/0.57    r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))),
% 1.68/0.57    inference(cnf_transformation,[],[f34])).
% 1.68/0.57  % SZS output end Proof for theBenchmark
% 1.68/0.57  % (24250)------------------------------
% 1.68/0.57  % (24250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.57  % (24250)Termination reason: Refutation
% 1.68/0.57  
% 1.68/0.57  % (24250)Memory used [KB]: 12153
% 1.68/0.57  % (24250)Time elapsed: 0.160 s
% 1.68/0.57  % (24250)------------------------------
% 1.68/0.57  % (24250)------------------------------
% 1.68/0.57  % (24238)Success in time 0.222 s
%------------------------------------------------------------------------------
