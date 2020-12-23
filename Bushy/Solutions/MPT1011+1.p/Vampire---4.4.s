%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t66_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:48 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  437 (2195 expanded)
%              Number of leaves         :  120 ( 806 expanded)
%              Depth                    :   14
%              Number of atoms          : 1437 (6074 expanded)
%              Number of equality atoms :  115 ( 335 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1337,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f89,f96,f103,f110,f117,f124,f140,f147,f159,f160,f180,f187,f199,f208,f219,f226,f236,f243,f254,f276,f296,f297,f319,f332,f348,f377,f390,f454,f467,f489,f503,f504,f511,f527,f546,f561,f568,f575,f598,f632,f645,f652,f659,f668,f701,f709,f710,f711,f712,f734,f747,f779,f795,f802,f809,f842,f849,f856,f870,f877,f1014,f1034,f1055,f1076,f1089,f1096,f1103,f1110,f1118,f1134,f1147,f1154,f1161,f1168,f1176,f1199,f1221,f1228,f1235,f1251,f1258,f1336])).

fof(f1336,plain,
    ( ~ spl8_0
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_10
    | spl8_51
    | ~ spl8_170 ),
    inference(avatar_contradiction_clause,[],[f1335])).

fof(f1335,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_51
    | ~ spl8_170 ),
    inference(subsumption_resolution,[],[f1334,f116])).

fof(f116,plain,
    ( v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_10
  <=> v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f1334,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_51
    | ~ spl8_170 ),
    inference(subsumption_resolution,[],[f1333,f88])).

fof(f88,plain,
    ( v1_funct_2(sK2,sK0,k1_tarski(sK1))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl8_2
  <=> v1_funct_2(sK2,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1333,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_tarski(sK1))
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_51
    | ~ spl8_170 ),
    inference(subsumption_resolution,[],[f1332,f81])).

fof(f81,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl8_0
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f1332,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_funct_2(sK2,sK0,k1_tarski(sK1))
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl8_8
    | ~ spl8_51
    | ~ spl8_170 ),
    inference(subsumption_resolution,[],[f1331,f312])).

fof(f312,plain,
    ( ~ r2_relset_1(sK0,k1_tarski(sK1),sK3,sK2)
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl8_51
  <=> ~ r2_relset_1(sK0,k1_tarski(sK1),sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f1331,plain,
    ( r2_relset_1(sK0,k1_tarski(sK1),sK3,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_funct_2(sK2,sK0,k1_tarski(sK1))
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl8_8
    | ~ spl8_170 ),
    inference(resolution,[],[f1117,f109])).

fof(f109,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl8_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f1117,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | r2_relset_1(sK0,X0,sK3,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ v1_funct_2(sK3,sK0,X0) )
    | ~ spl8_170 ),
    inference(avatar_component_clause,[],[f1116])).

fof(f1116,plain,
    ( spl8_170
  <=> ! [X0] :
        ( ~ v1_funct_2(sK3,sK0,X0)
        | r2_relset_1(sK0,X0,sK3,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_170])])).

fof(f1258,plain,
    ( ~ spl8_195
    | ~ spl8_190 ),
    inference(avatar_split_clause,[],[f1249,f1226,f1256])).

fof(f1256,plain,
    ( spl8_195
  <=> ~ sP7(sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_195])])).

fof(f1226,plain,
    ( spl8_190
  <=> r2_hidden(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))),sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_190])])).

fof(f1249,plain,
    ( ~ sP7(sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))))
    | ~ spl8_190 ),
    inference(resolution,[],[f1227,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP7(X1) ) ),
    inference(general_splitting,[],[f67,f73_D])).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP7(X1) ) ),
    inference(cnf_transformation,[],[f73_D])).

fof(f73_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t66_funct_2.p',t5_subset)).

fof(f1227,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))),sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))))
    | ~ spl8_190 ),
    inference(avatar_component_clause,[],[f1226])).

fof(f1251,plain,
    ( spl8_192
    | ~ spl8_190 ),
    inference(avatar_split_clause,[],[f1248,f1226,f1233])).

fof(f1233,plain,
    ( spl8_192
  <=> m1_subset_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))),sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_192])])).

fof(f1248,plain,
    ( m1_subset_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))),sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))))
    | ~ spl8_190 ),
    inference(resolution,[],[f1227,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t66_funct_2.p',t1_subset)).

fof(f1235,plain,
    ( spl8_192
    | ~ spl8_184 ),
    inference(avatar_split_clause,[],[f1208,f1197,f1233])).

fof(f1197,plain,
    ( spl8_184
  <=> sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_184])])).

fof(f1208,plain,
    ( m1_subset_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))),sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))))
    | ~ spl8_184 ),
    inference(superposition,[],[f59,f1198])).

fof(f1198,plain,
    ( sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))))
    | ~ spl8_184 ),
    inference(avatar_component_clause,[],[f1197])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t66_funct_2.p',existence_m1_subset_1)).

fof(f1228,plain,
    ( spl8_186
    | spl8_190
    | ~ spl8_184 ),
    inference(avatar_split_clause,[],[f1207,f1197,f1226,f1213])).

fof(f1213,plain,
    ( spl8_186
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_186])])).

fof(f1207,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))),sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))))
    | v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))))
    | ~ spl8_184 ),
    inference(superposition,[],[f127,f1198])).

fof(f127,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f69,f59])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t66_funct_2.p',t2_subset)).

fof(f1221,plain,
    ( spl8_186
    | ~ spl8_189
    | ~ spl8_184 ),
    inference(avatar_split_clause,[],[f1206,f1197,f1219,f1213])).

fof(f1219,plain,
    ( spl8_189
  <=> ~ r2_hidden(sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))),sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_189])])).

fof(f1206,plain,
    ( ~ r2_hidden(sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))),sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))
    | v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))))
    | ~ spl8_184 ),
    inference(superposition,[],[f161,f1198])).

fof(f161,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f127,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t66_funct_2.p',antisymmetry_r2_hidden)).

fof(f1199,plain,
    ( spl8_184
    | ~ spl8_116
    | spl8_137 ),
    inference(avatar_split_clause,[],[f1192,f844,f699,f1197])).

fof(f699,plain,
    ( spl8_116
  <=> v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_116])])).

fof(f844,plain,
    ( spl8_137
  <=> sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) != sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_137])])).

fof(f1192,plain,
    ( sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))))
    | ~ spl8_116
    | ~ spl8_137 ),
    inference(subsumption_resolution,[],[f1187,f845])).

fof(f845,plain,
    ( sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) != sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))))
    | ~ spl8_137 ),
    inference(avatar_component_clause,[],[f844])).

fof(f1187,plain,
    ( sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))))
    | sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))))
    | ~ spl8_116 ),
    inference(resolution,[],[f924,f700])).

fof(f700,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))
    | ~ spl8_116 ),
    inference(avatar_component_clause,[],[f699])).

fof(f924,plain,
    ( ! [X14] :
        ( ~ v1_xboole_0(X14)
        | sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(X14))))
        | sK4(k1_zfmisc_1(k1_zfmisc_1(X14))) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) )
    | ~ spl8_116 ),
    inference(resolution,[],[f723,f713])).

fof(f713,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = X0 )
    | ~ spl8_116 ),
    inference(resolution,[],[f700,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t66_funct_2.p',t8_boole)).

fof(f723,plain,
    ( ! [X2] :
        ( v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(X2))))
        | sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(X2))))
        | ~ v1_xboole_0(X2) )
    | ~ spl8_116 ),
    inference(resolution,[],[f713,f420])).

fof(f420,plain,(
    ! [X4] :
      ( v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(X4)))))
      | v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(X4))))
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f357,f163])).

fof(f163,plain,(
    ! [X2] :
      ( ~ sP7(X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f127,f74])).

fof(f357,plain,(
    ! [X10] :
      ( sP7(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(X10)))))
      | ~ v1_xboole_0(X10)
      | v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(X10)))) ) ),
    inference(resolution,[],[f349,f73])).

fof(f349,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK4(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK4(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f258,f127])).

fof(f258,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK4(k1_zfmisc_1(X3)))
      | m1_subset_1(X2,X3) ) ),
    inference(resolution,[],[f64,f59])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t66_funct_2.p',t4_subset)).

fof(f1176,plain,
    ( spl8_182
    | ~ spl8_177
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_174 ),
    inference(avatar_split_clause,[],[f1172,f1145,f122,f94,f1149,f1174])).

fof(f1174,plain,
    ( spl8_182
  <=> ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,X0)
        | r2_relset_1(sK0,X0,sK2,sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK3,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_182])])).

fof(f1149,plain,
    ( spl8_177
  <=> k1_funct_1(sK2,sK5(sK0,sK2,sK3)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_177])])).

fof(f94,plain,
    ( spl8_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f122,plain,
    ( spl8_12
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f1145,plain,
    ( spl8_174
  <=> k1_funct_1(sK3,sK5(sK0,sK2,sK3)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_174])])).

fof(f1172,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK5(sK0,sK2,sK3)) != sK1
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK3,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | r2_relset_1(sK0,X0,sK2,sK3) )
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_174 ),
    inference(subsumption_resolution,[],[f1171,f95])).

fof(f95,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f1171,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK5(sK0,sK2,sK3)) != sK1
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK3,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(sK2)
        | r2_relset_1(sK0,X0,sK2,sK3) )
    | ~ spl8_12
    | ~ spl8_174 ),
    inference(subsumption_resolution,[],[f1170,f123])).

fof(f123,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1170,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK5(sK0,sK2,sK3)) != sK1
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(sK2)
        | r2_relset_1(sK0,X0,sK2,sK3) )
    | ~ spl8_174 ),
    inference(superposition,[],[f63,f1146])).

fof(f1146,plain,
    ( k1_funct_1(sK3,sK5(sK0,sK2,sK3)) = sK1
    | ~ spl8_174 ),
    inference(avatar_component_clause,[],[f1145])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t66_funct_2.p',t18_funct_2)).

fof(f1168,plain,
    ( spl8_180
    | ~ spl8_172 ),
    inference(avatar_split_clause,[],[f1138,f1132,f1166])).

fof(f1166,plain,
    ( spl8_180
  <=> m1_subset_1(sK5(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_180])])).

fof(f1132,plain,
    ( spl8_172
  <=> r2_hidden(sK5(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_172])])).

fof(f1138,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK3),sK0)
    | ~ spl8_172 ),
    inference(resolution,[],[f1133,f65])).

fof(f1133,plain,
    ( r2_hidden(sK5(sK0,sK2,sK3),sK0)
    | ~ spl8_172 ),
    inference(avatar_component_clause,[],[f1132])).

fof(f1161,plain,
    ( ~ spl8_179
    | ~ spl8_172 ),
    inference(avatar_split_clause,[],[f1137,f1132,f1159])).

fof(f1159,plain,
    ( spl8_179
  <=> ~ r2_hidden(sK0,sK5(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_179])])).

fof(f1137,plain,
    ( ~ r2_hidden(sK0,sK5(sK0,sK2,sK3))
    | ~ spl8_172 ),
    inference(resolution,[],[f1133,f66])).

fof(f1154,plain,
    ( spl8_176
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_172 ),
    inference(avatar_split_clause,[],[f1136,f1132,f94,f87,f80,f1152])).

fof(f1152,plain,
    ( spl8_176
  <=> k1_funct_1(sK2,sK5(sK0,sK2,sK3)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_176])])).

fof(f1136,plain,
    ( k1_funct_1(sK2,sK5(sK0,sK2,sK3)) = sK1
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_172 ),
    inference(resolution,[],[f1133,f437])).

fof(f437,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,X0) = sK1 )
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f436,f95])).

fof(f436,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,X0) = sK1 )
    | ~ spl8_0
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f432,f88])).

fof(f432,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,X0) = sK1 )
    | ~ spl8_0 ),
    inference(resolution,[],[f60,f81])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(X3,X2) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t66_funct_2.p',t65_funct_2)).

fof(f1147,plain,
    ( spl8_174
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_172 ),
    inference(avatar_split_clause,[],[f1135,f1132,f122,f115,f108,f1145])).

fof(f1135,plain,
    ( k1_funct_1(sK3,sK5(sK0,sK2,sK3)) = sK1
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_172 ),
    inference(resolution,[],[f1133,f439])).

fof(f439,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK3,X1) = sK1 )
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f438,f123])).

fof(f438,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK3)
        | ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK3,X1) = sK1 )
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f433,f116])).

fof(f433,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK3)
        | ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK3,X1) = sK1 )
    | ~ spl8_8 ),
    inference(resolution,[],[f60,f109])).

fof(f1134,plain,
    ( spl8_172
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f1127,f122,f115,f108,f101,f94,f87,f80,f1132])).

fof(f101,plain,
    ( spl8_7
  <=> ~ r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f1127,plain,
    ( r2_hidden(sK5(sK0,sK2,sK3),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f1126,f102])).

fof(f102,plain,
    ( ~ r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f1126,plain,
    ( r2_hidden(sK5(sK0,sK2,sK3),sK0)
    | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f1125,f95])).

fof(f1125,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK5(sK0,sK2,sK3),sK0)
    | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f1120,f88])).

fof(f1120,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK5(sK0,sK2,sK3),sK0)
    | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(resolution,[],[f865,f81])).

fof(f865,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_2(X1,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(X1)
        | r2_hidden(sK5(sK0,X1,sK3),sK0)
        | r2_relset_1(sK0,k1_tarski(sK1),X1,sK3) )
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f864,f116])).

fof(f864,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(X1)
        | r2_hidden(sK5(sK0,X1,sK3),sK0)
        | r2_relset_1(sK0,k1_tarski(sK1),X1,sK3) )
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f858,f123])).

fof(f858,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(X1)
        | r2_hidden(sK5(sK0,X1,sK3),sK0)
        | r2_relset_1(sK0,k1_tarski(sK1),X1,sK3) )
    | ~ spl8_8 ),
    inference(resolution,[],[f62,f109])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2)
      | r2_hidden(sK5(X0,X2,X3),X0)
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1118,plain,
    ( spl8_170
    | ~ spl8_165
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_162 ),
    inference(avatar_split_clause,[],[f1114,f1087,f122,f94,f1091,f1116])).

fof(f1091,plain,
    ( spl8_165
  <=> k1_funct_1(sK2,sK5(sK0,sK3,sK2)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_165])])).

fof(f1087,plain,
    ( spl8_162
  <=> k1_funct_1(sK3,sK5(sK0,sK3,sK2)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_162])])).

fof(f1114,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK5(sK0,sK3,sK2)) != sK1
        | ~ v1_funct_2(sK3,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | r2_relset_1(sK0,X0,sK3,sK2) )
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_162 ),
    inference(subsumption_resolution,[],[f1113,f123])).

fof(f1113,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK5(sK0,sK3,sK2)) != sK1
        | ~ v1_funct_2(sK3,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(sK3)
        | r2_relset_1(sK0,X0,sK3,sK2) )
    | ~ spl8_4
    | ~ spl8_162 ),
    inference(subsumption_resolution,[],[f1112,f95])).

fof(f1112,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK5(sK0,sK3,sK2)) != sK1
        | ~ v1_funct_2(sK3,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(sK3)
        | r2_relset_1(sK0,X0,sK3,sK2) )
    | ~ spl8_162 ),
    inference(superposition,[],[f63,f1088])).

fof(f1088,plain,
    ( k1_funct_1(sK3,sK5(sK0,sK3,sK2)) = sK1
    | ~ spl8_162 ),
    inference(avatar_component_clause,[],[f1087])).

fof(f1110,plain,
    ( spl8_168
    | ~ spl8_142 ),
    inference(avatar_split_clause,[],[f1080,f1012,f1108])).

fof(f1108,plain,
    ( spl8_168
  <=> m1_subset_1(sK5(sK0,sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_168])])).

fof(f1012,plain,
    ( spl8_142
  <=> r2_hidden(sK5(sK0,sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_142])])).

fof(f1080,plain,
    ( m1_subset_1(sK5(sK0,sK3,sK2),sK0)
    | ~ spl8_142 ),
    inference(resolution,[],[f1013,f65])).

fof(f1013,plain,
    ( r2_hidden(sK5(sK0,sK3,sK2),sK0)
    | ~ spl8_142 ),
    inference(avatar_component_clause,[],[f1012])).

fof(f1103,plain,
    ( ~ spl8_167
    | ~ spl8_142 ),
    inference(avatar_split_clause,[],[f1079,f1012,f1101])).

fof(f1101,plain,
    ( spl8_167
  <=> ~ r2_hidden(sK0,sK5(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_167])])).

fof(f1079,plain,
    ( ~ r2_hidden(sK0,sK5(sK0,sK3,sK2))
    | ~ spl8_142 ),
    inference(resolution,[],[f1013,f66])).

fof(f1096,plain,
    ( spl8_164
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_142 ),
    inference(avatar_split_clause,[],[f1078,f1012,f94,f87,f80,f1094])).

fof(f1094,plain,
    ( spl8_164
  <=> k1_funct_1(sK2,sK5(sK0,sK3,sK2)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_164])])).

fof(f1078,plain,
    ( k1_funct_1(sK2,sK5(sK0,sK3,sK2)) = sK1
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_142 ),
    inference(resolution,[],[f1013,f437])).

fof(f1089,plain,
    ( spl8_162
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_142 ),
    inference(avatar_split_clause,[],[f1077,f1012,f122,f115,f108,f1087])).

fof(f1077,plain,
    ( k1_funct_1(sK3,sK5(sK0,sK3,sK2)) = sK1
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_142 ),
    inference(resolution,[],[f1013,f439])).

fof(f1076,plain,
    ( spl8_156
    | ~ spl8_159
    | ~ spl8_161
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | spl8_103
    | spl8_107 ),
    inference(avatar_split_clause,[],[f1057,f643,f627,f94,f87,f80,f1074,f1068,f1062])).

fof(f1062,plain,
    ( spl8_156
  <=> r2_hidden(sK5(sK0,sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_156])])).

fof(f1068,plain,
    ( spl8_159
  <=> ~ v1_funct_1(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_159])])).

fof(f1074,plain,
    ( spl8_161
  <=> ~ v1_funct_2(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_161])])).

fof(f627,plain,
    ( spl8_103
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).

fof(f643,plain,
    ( spl8_107
  <=> ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_107])])).

fof(f1057,plain,
    ( ~ v1_funct_2(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))))
    | r2_hidden(sK5(sK0,sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK2),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_103
    | ~ spl8_107 ),
    inference(subsumption_resolution,[],[f1056,f628])).

fof(f628,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))))
    | ~ spl8_103 ),
    inference(avatar_component_clause,[],[f627])).

fof(f1056,plain,
    ( ~ v1_funct_2(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))))
    | r2_hidden(sK5(sK0,sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK2),sK0)
    | v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))))
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_107 ),
    inference(subsumption_resolution,[],[f1004,f644])).

fof(f644,plain,
    ( ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK2)
    | ~ spl8_107 ),
    inference(avatar_component_clause,[],[f643])).

fof(f1004,plain,
    ( ~ v1_funct_2(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))))
    | r2_hidden(sK5(sK0,sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK2),sK0)
    | r2_relset_1(sK0,k1_tarski(sK1),sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK2)
    | v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))))
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f863,f408])).

fof(f408,plain,(
    ! [X4] :
      ( m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(X4))))),X4)
      | v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(X4))))) ) ),
    inference(resolution,[],[f358,f258])).

fof(f358,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK4(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK4(k1_zfmisc_1(X0))) ) ),
    inference(subsumption_resolution,[],[f350,f188])).

fof(f188,plain,(
    ! [X0] :
      ( v1_xboole_0(sK4(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f167,f163])).

fof(f167,plain,(
    ! [X0] :
      ( sP7(sK4(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f73,f59])).

fof(f350,plain,(
    ! [X0] :
      ( v1_xboole_0(sK4(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0)
      | r2_hidden(sK4(sK4(k1_zfmisc_1(X0))),X0) ) ),
    inference(resolution,[],[f349,f69])).

fof(f863,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_2(X0,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(X0)
        | r2_hidden(sK5(sK0,X0,sK2),sK0)
        | r2_relset_1(sK0,k1_tarski(sK1),X0,sK2) )
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f862,f88])).

fof(f862,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_2(sK2,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(X0)
        | r2_hidden(sK5(sK0,X0,sK2),sK0)
        | r2_relset_1(sK0,k1_tarski(sK1),X0,sK2) )
    | ~ spl8_0
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f857,f95])).

fof(f857,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(X0)
        | r2_hidden(sK5(sK0,X0,sK2),sK0)
        | r2_relset_1(sK0,k1_tarski(sK1),X0,sK2) )
    | ~ spl8_0 ),
    inference(resolution,[],[f62,f81])).

fof(f1055,plain,
    ( spl8_150
    | ~ spl8_153
    | ~ spl8_155
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | spl8_67
    | spl8_69 ),
    inference(avatar_split_clause,[],[f1036,f382,f372,f94,f87,f80,f1053,f1047,f1041])).

fof(f1041,plain,
    ( spl8_150
  <=> r2_hidden(sK5(sK0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_150])])).

fof(f1047,plain,
    ( spl8_153
  <=> ~ v1_funct_1(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_153])])).

fof(f1053,plain,
    ( spl8_155
  <=> ~ v1_funct_2(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))),sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_155])])).

fof(f372,plain,
    ( spl8_67
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f382,plain,
    ( spl8_69
  <=> ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).

fof(f1036,plain,
    ( ~ v1_funct_2(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))),sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))
    | r2_hidden(sK5(sK0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))),sK2),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_67
    | ~ spl8_69 ),
    inference(subsumption_resolution,[],[f1035,f373])).

fof(f373,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))
    | ~ spl8_67 ),
    inference(avatar_component_clause,[],[f372])).

fof(f1035,plain,
    ( ~ v1_funct_2(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))),sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))
    | r2_hidden(sK5(sK0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))),sK2),sK0)
    | v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_69 ),
    inference(subsumption_resolution,[],[f1003,f383])).

fof(f383,plain,
    ( ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))),sK2)
    | ~ spl8_69 ),
    inference(avatar_component_clause,[],[f382])).

fof(f1003,plain,
    ( ~ v1_funct_2(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))),sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))
    | r2_hidden(sK5(sK0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))),sK2),sK0)
    | r2_relset_1(sK0,k1_tarski(sK1),sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))),sK2)
    | v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f863,f349])).

fof(f1034,plain,
    ( spl8_144
    | ~ spl8_147
    | ~ spl8_149
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | spl8_55 ),
    inference(avatar_split_clause,[],[f1015,f324,f94,f87,f80,f1032,f1026,f1020])).

fof(f1020,plain,
    ( spl8_144
  <=> r2_hidden(sK5(sK0,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_144])])).

fof(f1026,plain,
    ( spl8_147
  <=> ~ v1_funct_1(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_147])])).

fof(f1032,plain,
    ( spl8_149
  <=> ~ v1_funct_2(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))),sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_149])])).

fof(f324,plain,
    ( spl8_55
  <=> ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f1015,plain,
    ( ~ v1_funct_2(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))),sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))
    | r2_hidden(sK5(sK0,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))),sK2),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_55 ),
    inference(subsumption_resolution,[],[f1002,f325])).

fof(f325,plain,
    ( ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))),sK2)
    | ~ spl8_55 ),
    inference(avatar_component_clause,[],[f324])).

fof(f1002,plain,
    ( ~ v1_funct_2(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))),sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))
    | r2_hidden(sK5(sK0,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))),sK2),sK0)
    | r2_relset_1(sK0,k1_tarski(sK1),sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))),sK2)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f863,f59])).

fof(f1014,plain,
    ( spl8_142
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | spl8_51 ),
    inference(avatar_split_clause,[],[f1007,f311,f122,f115,f108,f94,f87,f80,f1012])).

fof(f1007,plain,
    ( r2_hidden(sK5(sK0,sK3,sK2),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_51 ),
    inference(subsumption_resolution,[],[f1006,f312])).

fof(f1006,plain,
    ( r2_hidden(sK5(sK0,sK3,sK2),sK0)
    | r2_relset_1(sK0,k1_tarski(sK1),sK3,sK2)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f1005,f123])).

fof(f1005,plain,
    ( ~ v1_funct_1(sK3)
    | r2_hidden(sK5(sK0,sK3,sK2),sK0)
    | r2_relset_1(sK0,k1_tarski(sK1),sK3,sK2)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f1001,f116])).

fof(f1001,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK3)
    | r2_hidden(sK5(sK0,sK3,sK2),sK0)
    | r2_relset_1(sK0,k1_tarski(sK1),sK3,sK2)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(resolution,[],[f863,f109])).

fof(f877,plain,
    ( ~ spl8_141
    | ~ spl8_130 ),
    inference(avatar_split_clause,[],[f868,f800,f875])).

fof(f875,plain,
    ( spl8_141
  <=> ~ sP7(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_141])])).

fof(f800,plain,
    ( spl8_130
  <=> r2_hidden(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_130])])).

fof(f868,plain,
    ( ~ sP7(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))
    | ~ spl8_130 ),
    inference(resolution,[],[f801,f74])).

fof(f801,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))
    | ~ spl8_130 ),
    inference(avatar_component_clause,[],[f800])).

fof(f870,plain,
    ( spl8_132
    | ~ spl8_130 ),
    inference(avatar_split_clause,[],[f867,f800,f807])).

fof(f807,plain,
    ( spl8_132
  <=> m1_subset_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_132])])).

fof(f867,plain,
    ( m1_subset_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))
    | ~ spl8_130 ),
    inference(resolution,[],[f801,f65])).

fof(f856,plain,
    ( spl8_138
    | ~ spl8_116
    | ~ spl8_126 ),
    inference(avatar_split_clause,[],[f835,f787,f699,f854])).

fof(f854,plain,
    ( spl8_138
  <=> sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_138])])).

fof(f787,plain,
    ( spl8_126
  <=> v1_xboole_0(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_126])])).

fof(f835,plain,
    ( sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))))))
    | ~ spl8_116
    | ~ spl8_126 ),
    inference(resolution,[],[f788,f716])).

fof(f716,plain,
    ( ! [X3] :
        ( ~ v1_xboole_0(X3)
        | sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(X3)))) )
    | ~ spl8_116 ),
    inference(resolution,[],[f700,f412])).

fof(f412,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(X0)))) = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f411,f167])).

fof(f411,plain,(
    ! [X2,X3] :
      ( ~ sP7(X2)
      | sK4(k1_zfmisc_1(X2)) = X3
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f406,f61])).

fof(f406,plain,(
    ! [X2] :
      ( v1_xboole_0(sK4(k1_zfmisc_1(X2)))
      | ~ sP7(X2) ) ),
    inference(resolution,[],[f358,f74])).

fof(f788,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))
    | ~ spl8_126 ),
    inference(avatar_component_clause,[],[f787])).

fof(f849,plain,
    ( spl8_136
    | ~ spl8_116
    | ~ spl8_126 ),
    inference(avatar_split_clause,[],[f834,f787,f699,f847])).

fof(f847,plain,
    ( spl8_136
  <=> sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_136])])).

fof(f834,plain,
    ( sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))))
    | ~ spl8_116
    | ~ spl8_126 ),
    inference(resolution,[],[f788,f714])).

fof(f714,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | sK4(k1_zfmisc_1(X1)) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) )
    | ~ spl8_116 ),
    inference(resolution,[],[f700,f190])).

fof(f190,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | sK4(k1_zfmisc_1(X1)) = X2
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f188,f61])).

fof(f842,plain,
    ( spl8_134
    | ~ spl8_116
    | ~ spl8_126 ),
    inference(avatar_split_clause,[],[f833,f787,f699,f840])).

fof(f840,plain,
    ( spl8_134
  <=> k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).

fof(f833,plain,
    ( k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))
    | ~ spl8_116
    | ~ spl8_126 ),
    inference(resolution,[],[f788,f713])).

fof(f809,plain,
    ( spl8_132
    | ~ spl8_120 ),
    inference(avatar_split_clause,[],[f768,f732,f807])).

fof(f732,plain,
    ( spl8_120
  <=> sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_120])])).

fof(f768,plain,
    ( m1_subset_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))
    | ~ spl8_120 ),
    inference(superposition,[],[f59,f733])).

fof(f733,plain,
    ( sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))
    | ~ spl8_120 ),
    inference(avatar_component_clause,[],[f732])).

fof(f802,plain,
    ( spl8_126
    | spl8_130
    | ~ spl8_120 ),
    inference(avatar_split_clause,[],[f767,f732,f800,f787])).

fof(f767,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))
    | v1_xboole_0(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))
    | ~ spl8_120 ),
    inference(superposition,[],[f127,f733])).

fof(f795,plain,
    ( spl8_126
    | ~ spl8_129
    | ~ spl8_120 ),
    inference(avatar_split_clause,[],[f766,f732,f793,f787])).

fof(f793,plain,
    ( spl8_129
  <=> ~ r2_hidden(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))),sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_129])])).

fof(f766,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))),sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))
    | v1_xboole_0(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))
    | ~ spl8_120 ),
    inference(superposition,[],[f161,f733])).

fof(f779,plain,
    ( spl8_124
    | ~ spl8_116
    | ~ spl8_120 ),
    inference(avatar_split_clause,[],[f772,f732,f699,f777])).

fof(f777,plain,
    ( spl8_124
  <=> sP7(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_124])])).

fof(f772,plain,
    ( sP7(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))
    | ~ spl8_116
    | ~ spl8_120 ),
    inference(subsumption_resolution,[],[f757,f700])).

fof(f757,plain,
    ( sP7(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))
    | ~ v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))
    | ~ spl8_120 ),
    inference(superposition,[],[f167,f733])).

fof(f747,plain,
    ( spl8_122
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f739,f699,f745])).

fof(f745,plain,
    ( spl8_122
  <=> sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).

fof(f739,plain,
    ( sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))))
    | ~ spl8_116 ),
    inference(resolution,[],[f716,f700])).

fof(f734,plain,
    ( spl8_120
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f726,f699,f732])).

fof(f726,plain,
    ( sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))))
    | ~ spl8_116 ),
    inference(resolution,[],[f714,f700])).

fof(f712,plain,
    ( ~ spl8_73
    | spl8_77 ),
    inference(avatar_split_clause,[],[f600,f456,f443])).

fof(f443,plain,
    ( spl8_73
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).

fof(f456,plain,
    ( spl8_77
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f600,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_77 ),
    inference(resolution,[],[f457,f188])).

fof(f457,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK0)))
    | ~ spl8_77 ),
    inference(avatar_component_clause,[],[f456])).

fof(f711,plain,
    ( spl8_114
    | spl8_116
    | spl8_72
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f686,f122,f115,f108,f446,f699,f693])).

fof(f693,plain,
    ( spl8_114
  <=> k1_funct_1(sK3,sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_114])])).

fof(f446,plain,
    ( spl8_72
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f686,plain,
    ( v1_xboole_0(sK0)
    | v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))
    | k1_funct_1(sK3,sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))) = sK1
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(resolution,[],[f602,f439])).

fof(f602,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(X0))))),X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(X0))))) ) ),
    inference(resolution,[],[f408,f69])).

fof(f710,plain,
    ( spl8_118
    | spl8_116
    | spl8_72
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f687,f94,f87,f80,f446,f699,f707])).

fof(f707,plain,
    ( spl8_118
  <=> k1_funct_1(sK2,sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_118])])).

fof(f687,plain,
    ( v1_xboole_0(sK0)
    | v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))
    | k1_funct_1(sK2,sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))) = sK1
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f602,f437])).

fof(f709,plain,
    ( spl8_118
    | spl8_116
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | spl8_73 ),
    inference(avatar_split_clause,[],[f702,f443,f94,f87,f80,f699,f707])).

fof(f702,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))
    | k1_funct_1(sK2,sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))) = sK1
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_73 ),
    inference(subsumption_resolution,[],[f687,f444])).

fof(f444,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_73 ),
    inference(avatar_component_clause,[],[f443])).

fof(f701,plain,
    ( spl8_114
    | spl8_116
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | spl8_73 ),
    inference(avatar_split_clause,[],[f688,f443,f122,f115,f108,f699,f693])).

fof(f688,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))
    | k1_funct_1(sK3,sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))))) = sK1
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_73 ),
    inference(subsumption_resolution,[],[f686,f444])).

fof(f668,plain,
    ( ~ spl8_113
    | spl8_103 ),
    inference(avatar_split_clause,[],[f660,f627,f666])).

fof(f666,plain,
    ( spl8_113
  <=> ~ sP7(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f660,plain,
    ( ~ sP7(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))
    | ~ spl8_103 ),
    inference(resolution,[],[f628,f406])).

fof(f659,plain,
    ( ~ spl8_107
    | spl8_110
    | spl8_102
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f611,f80,f630,f657,f643])).

fof(f657,plain,
    ( spl8_110
  <=> sK2 = sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_110])])).

fof(f630,plain,
    ( spl8_102
  <=> v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f611,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))))
    | sK2 = sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))))
    | ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK2)
    | ~ spl8_0 ),
    inference(resolution,[],[f408,f298])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | sK2 = X0
        | ~ r2_relset_1(sK0,k1_tarski(sK1),X0,sK2) )
    | ~ spl8_0 ),
    inference(resolution,[],[f56,f81])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t66_funct_2.p',redefinition_r2_relset_1)).

fof(f652,plain,
    ( ~ spl8_101
    | spl8_108
    | spl8_102
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f610,f108,f630,f650,f624])).

fof(f624,plain,
    ( spl8_101
  <=> ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f650,plain,
    ( spl8_108
  <=> sK3 = sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_108])])).

fof(f610,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))))
    | sK3 = sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))))
    | ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK3)
    | ~ spl8_8 ),
    inference(resolution,[],[f408,f299])).

fof(f299,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | sK3 = X1
        | ~ r2_relset_1(sK0,k1_tarski(sK1),X1,sK3) )
    | ~ spl8_8 ),
    inference(resolution,[],[f56,f109])).

fof(f645,plain,
    ( spl8_104
    | ~ spl8_107
    | spl8_102
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f609,f80,f630,f643,f637])).

fof(f637,plain,
    ( spl8_104
  <=> r2_relset_1(sK0,k1_tarski(sK1),sK2,sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).

fof(f609,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))))
    | ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK2)
    | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))))
    | ~ spl8_0 ),
    inference(resolution,[],[f408,f392])).

fof(f392,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ r2_relset_1(sK0,k1_tarski(sK1),X0,sK2)
        | r2_relset_1(sK0,k1_tarski(sK1),sK2,X0) )
    | ~ spl8_0 ),
    inference(resolution,[],[f57,f81])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | r2_relset_1(X0,X1,X3,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
       => r2_relset_1(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t66_funct_2.p',symmetry_r2_relset_1)).

fof(f632,plain,
    ( spl8_98
    | ~ spl8_101
    | spl8_102
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f608,f108,f630,f624,f618])).

fof(f618,plain,
    ( spl8_98
  <=> r2_relset_1(sK0,k1_tarski(sK1),sK3,sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_98])])).

fof(f608,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))))
    | ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))),sK3)
    | r2_relset_1(sK0,k1_tarski(sK1),sK3,sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))))
    | ~ spl8_8 ),
    inference(resolution,[],[f408,f393])).

fof(f393,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ r2_relset_1(sK0,k1_tarski(sK1),X1,sK3)
        | r2_relset_1(sK0,k1_tarski(sK1),sK3,X1) )
    | ~ spl8_8 ),
    inference(resolution,[],[f57,f109])).

fof(f598,plain,
    ( spl8_96
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f590,f459,f596])).

fof(f596,plain,
    ( spl8_96
  <=> sK4(k1_zfmisc_1(sK0)) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_96])])).

fof(f459,plain,
    ( spl8_76
  <=> v1_xboole_0(sK4(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f590,plain,
    ( sK4(k1_zfmisc_1(sK0)) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK0))))
    | ~ spl8_76 ),
    inference(resolution,[],[f583,f460])).

fof(f460,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK0)))
    | ~ spl8_76 ),
    inference(avatar_component_clause,[],[f459])).

fof(f583,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | sK4(k1_zfmisc_1(sK0)) = sK4(k1_zfmisc_1(X1)) )
    | ~ spl8_76 ),
    inference(resolution,[],[f521,f188])).

fof(f521,plain,
    ( ! [X4] :
        ( ~ v1_xboole_0(X4)
        | sK4(k1_zfmisc_1(sK0)) = X4 )
    | ~ spl8_76 ),
    inference(resolution,[],[f460,f61])).

fof(f575,plain,
    ( spl8_94
    | ~ spl8_80 ),
    inference(avatar_split_clause,[],[f538,f487,f573])).

fof(f573,plain,
    ( spl8_94
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f487,plain,
    ( spl8_80
  <=> sK0 = sK4(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f538,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl8_80 ),
    inference(superposition,[],[f59,f488])).

fof(f488,plain,
    ( sK0 = sK4(k1_zfmisc_1(sK0))
    | ~ spl8_80 ),
    inference(avatar_component_clause,[],[f487])).

fof(f568,plain,
    ( spl8_88
    | spl8_92
    | ~ spl8_80 ),
    inference(avatar_split_clause,[],[f537,f487,f566,f553])).

fof(f553,plain,
    ( spl8_88
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f566,plain,
    ( spl8_92
  <=> r2_hidden(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f537,plain,
    ( r2_hidden(sK0,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl8_80 ),
    inference(superposition,[],[f127,f488])).

fof(f561,plain,
    ( spl8_88
    | ~ spl8_91
    | ~ spl8_80 ),
    inference(avatar_split_clause,[],[f536,f487,f559,f553])).

fof(f559,plain,
    ( spl8_91
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).

fof(f536,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK0)
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl8_80 ),
    inference(superposition,[],[f161,f488])).

fof(f546,plain,
    ( spl8_86
    | ~ spl8_72
    | ~ spl8_80 ),
    inference(avatar_split_clause,[],[f539,f487,f446,f544])).

fof(f544,plain,
    ( spl8_86
  <=> sP7(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f539,plain,
    ( sP7(sK0)
    | ~ spl8_72
    | ~ spl8_80 ),
    inference(subsumption_resolution,[],[f529,f447])).

fof(f447,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f446])).

fof(f529,plain,
    ( sP7(sK0)
    | ~ v1_xboole_0(sK0)
    | ~ spl8_80 ),
    inference(superposition,[],[f167,f488])).

fof(f527,plain,
    ( spl8_80
    | ~ spl8_72
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f524,f459,f446,f487])).

fof(f524,plain,
    ( sK0 = sK4(k1_zfmisc_1(sK0))
    | ~ spl8_72
    | ~ spl8_76 ),
    inference(resolution,[],[f516,f460])).

fof(f516,plain,
    ( ! [X4] :
        ( ~ v1_xboole_0(X4)
        | sK0 = X4 )
    | ~ spl8_72 ),
    inference(resolution,[],[f447,f61])).

fof(f511,plain,
    ( spl8_76
    | spl8_84
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f495,f122,f115,f108,f509,f459])).

fof(f509,plain,
    ( spl8_84
  <=> k1_funct_1(sK3,sK4(sK4(k1_zfmisc_1(sK0)))) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f495,plain,
    ( k1_funct_1(sK3,sK4(sK4(k1_zfmisc_1(sK0)))) = sK1
    | v1_xboole_0(sK4(k1_zfmisc_1(sK0)))
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(resolution,[],[f439,f358])).

fof(f504,plain,
    ( spl8_72
    | spl8_82
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f494,f122,f115,f108,f501,f446])).

fof(f501,plain,
    ( spl8_82
  <=> k1_funct_1(sK3,sK4(sK0)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f494,plain,
    ( k1_funct_1(sK3,sK4(sK0)) = sK1
    | v1_xboole_0(sK0)
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(resolution,[],[f439,f127])).

fof(f503,plain,
    ( spl8_82
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | spl8_73 ),
    inference(avatar_split_clause,[],[f496,f443,f122,f115,f108,f501])).

fof(f496,plain,
    ( k1_funct_1(sK3,sK4(sK0)) = sK1
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_73 ),
    inference(subsumption_resolution,[],[f494,f444])).

fof(f489,plain,
    ( spl8_80
    | ~ spl8_72
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f480,f459,f446,f487])).

fof(f480,plain,
    ( sK0 = sK4(k1_zfmisc_1(sK0))
    | ~ spl8_72
    | ~ spl8_76 ),
    inference(resolution,[],[f472,f460])).

fof(f472,plain,
    ( ! [X4] :
        ( ~ v1_xboole_0(X4)
        | sK0 = X4 )
    | ~ spl8_72 ),
    inference(resolution,[],[f447,f61])).

fof(f467,plain,
    ( spl8_76
    | spl8_78
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f441,f94,f87,f80,f465,f459])).

fof(f465,plain,
    ( spl8_78
  <=> k1_funct_1(sK2,sK4(sK4(k1_zfmisc_1(sK0)))) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f441,plain,
    ( k1_funct_1(sK2,sK4(sK4(k1_zfmisc_1(sK0)))) = sK1
    | v1_xboole_0(sK4(k1_zfmisc_1(sK0)))
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f437,f358])).

fof(f454,plain,
    ( spl8_72
    | spl8_74
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f440,f94,f87,f80,f452,f446])).

fof(f452,plain,
    ( spl8_74
  <=> k1_funct_1(sK2,sK4(sK0)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f440,plain,
    ( k1_funct_1(sK2,sK4(sK0)) = sK1
    | v1_xboole_0(sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f437,f127])).

fof(f390,plain,
    ( ~ spl8_69
    | spl8_70
    | spl8_66
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f355,f80,f375,f388,f382])).

fof(f388,plain,
    ( spl8_70
  <=> sK2 = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f375,plain,
    ( spl8_66
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f355,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))
    | sK2 = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))
    | ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))),sK2)
    | ~ spl8_0 ),
    inference(resolution,[],[f349,f298])).

fof(f377,plain,
    ( ~ spl8_63
    | spl8_64
    | spl8_66
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f354,f108,f375,f369,f363])).

fof(f363,plain,
    ( spl8_63
  <=> ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f369,plain,
    ( spl8_64
  <=> sK3 = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f354,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))
    | sK3 = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))
    | ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))),sK3)
    | ~ spl8_8 ),
    inference(resolution,[],[f349,f299])).

fof(f348,plain,
    ( ~ spl8_59
    | spl8_60
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f335,f108,f346,f340])).

fof(f340,plain,
    ( spl8_59
  <=> ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f346,plain,
    ( spl8_60
  <=> sK3 = sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f335,plain,
    ( sK3 = sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))),sK3)
    | ~ spl8_8 ),
    inference(resolution,[],[f299,f59])).

fof(f332,plain,
    ( ~ spl8_55
    | spl8_56
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f306,f80,f330,f324])).

fof(f330,plain,
    ( spl8_56
  <=> sK2 = sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f306,plain,
    ( sK2 = sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))),sK2)
    | ~ spl8_0 ),
    inference(resolution,[],[f298,f59])).

fof(f319,plain,
    ( ~ spl8_51
    | spl8_52
    | ~ spl8_0
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f305,f108,f80,f317,f311])).

fof(f317,plain,
    ( spl8_52
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f305,plain,
    ( sK2 = sK3
    | ~ r2_relset_1(sK0,k1_tarski(sK1),sK3,sK2)
    | ~ spl8_0
    | ~ spl8_8 ),
    inference(resolution,[],[f298,f109])).

fof(f297,plain,
    ( ~ spl8_49
    | ~ spl8_0
    | spl8_25 ),
    inference(avatar_split_clause,[],[f283,f178,f80,f294])).

fof(f294,plain,
    ( spl8_49
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f178,plain,
    ( spl8_25
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f283,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2)
    | ~ spl8_0
    | ~ spl8_25 ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2)
    | ~ r2_hidden(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2)
    | ~ spl8_0
    | ~ spl8_25 ),
    inference(resolution,[],[f263,f260])).

fof(f260,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,k1_tarski(sK1)))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_0
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f259,f179])).

fof(f179,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_tarski(sK1)))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f178])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | v1_xboole_0(k2_zfmisc_1(sK0,k1_tarski(sK1)))
        | r2_hidden(X0,k2_zfmisc_1(sK0,k1_tarski(sK1))) )
    | ~ spl8_0 ),
    inference(resolution,[],[f256,f69])).

fof(f256,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(sK0,k1_tarski(sK1)))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_0 ),
    inference(resolution,[],[f64,f81])).

fof(f263,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k2_zfmisc_1(sK0,k1_tarski(sK1)),X0)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_0
    | ~ spl8_25 ),
    inference(resolution,[],[f260,f66])).

fof(f296,plain,
    ( ~ spl8_47
    | ~ spl8_49
    | ~ spl8_0
    | ~ spl8_8
    | spl8_25 ),
    inference(avatar_split_clause,[],[f281,f178,f108,f80,f294,f288])).

fof(f288,plain,
    ( spl8_47
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f281,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2)
    | ~ r2_hidden(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK3)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_25 ),
    inference(resolution,[],[f263,f262])).

fof(f262,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,k1_tarski(sK1)))
        | ~ r2_hidden(X0,sK3) )
    | ~ spl8_8
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f261,f179])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | v1_xboole_0(k2_zfmisc_1(sK0,k1_tarski(sK1)))
        | r2_hidden(X0,k2_zfmisc_1(sK0,k1_tarski(sK1))) )
    | ~ spl8_8 ),
    inference(resolution,[],[f257,f69])).

fof(f257,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k2_zfmisc_1(sK0,k1_tarski(sK1)))
        | ~ r2_hidden(X1,sK3) )
    | ~ spl8_8 ),
    inference(resolution,[],[f64,f109])).

fof(f276,plain,
    ( ~ spl8_43
    | spl8_44
    | ~ spl8_0
    | spl8_25 ),
    inference(avatar_split_clause,[],[f265,f178,f80,f274,f271])).

fof(f271,plain,
    ( spl8_43
  <=> ~ sP7(k2_zfmisc_1(sK0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f274,plain,
    ( spl8_44
  <=> ! [X2] : ~ r2_hidden(X2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f265,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | ~ sP7(k2_zfmisc_1(sK0,k1_tarski(sK1))) )
    | ~ spl8_0
    | ~ spl8_25 ),
    inference(resolution,[],[f260,f74])).

fof(f254,plain,
    ( ~ spl8_41
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f244,f145,f252])).

fof(f252,plain,
    ( spl8_41
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f145,plain,
    ( spl8_18
  <=> r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f244,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))),sK3)
    | ~ spl8_18 ),
    inference(resolution,[],[f146,f66])).

fof(f146,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f145])).

fof(f243,plain,
    ( spl8_38
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f228,f108,f241])).

fof(f241,plain,
    ( spl8_38
  <=> r2_relset_1(sK0,k1_tarski(sK1),sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f228,plain,
    ( r2_relset_1(sK0,k1_tarski(sK1),sK3,sK3)
    | ~ spl8_8 ),
    inference(resolution,[],[f75,f109])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f236,plain,
    ( spl8_36
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f227,f80,f234])).

fof(f234,plain,
    ( spl8_36
  <=> r2_relset_1(sK0,k1_tarski(sK1),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f227,plain,
    ( r2_relset_1(sK0,k1_tarski(sK1),sK2,sK2)
    | ~ spl8_0 ),
    inference(resolution,[],[f75,f81])).

fof(f226,plain,
    ( ~ spl8_35
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f211,f132,f224])).

fof(f224,plain,
    ( spl8_35
  <=> ~ sP7(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f132,plain,
    ( spl8_14
  <=> r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f211,plain,
    ( ~ sP7(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl8_14 ),
    inference(resolution,[],[f133,f74])).

fof(f133,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f219,plain,
    ( ~ spl8_33
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f209,f132,f217])).

fof(f217,plain,
    ( spl8_33
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f209,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))),sK2)
    | ~ spl8_14 ),
    inference(resolution,[],[f133,f66])).

fof(f208,plain,
    ( spl8_30
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f200,f138,f206])).

fof(f206,plain,
    ( spl8_30
  <=> k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f138,plain,
    ( spl8_16
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f200,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))))
    | ~ spl8_16 ),
    inference(resolution,[],[f192,f139])).

fof(f139,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f138])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))) = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(X0)))) )
    | ~ spl8_16 ),
    inference(resolution,[],[f189,f188])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))) = sK4(k1_zfmisc_1(X0)) )
    | ~ spl8_16 ),
    inference(resolution,[],[f188,f148])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))) = X0 )
    | ~ spl8_16 ),
    inference(resolution,[],[f139,f61])).

fof(f199,plain,
    ( spl8_28
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f191,f138,f197])).

fof(f197,plain,
    ( spl8_28
  <=> k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))) = sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f191,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))) = sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))))
    | ~ spl8_16 ),
    inference(resolution,[],[f189,f139])).

fof(f187,plain,
    ( spl8_26
    | ~ spl8_25
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f166,f108,f178,f185])).

fof(f185,plain,
    ( spl8_26
  <=> sP7(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f166,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_tarski(sK1)))
    | sP7(sK3)
    | ~ spl8_8 ),
    inference(resolution,[],[f73,f109])).

fof(f180,plain,
    ( spl8_22
    | ~ spl8_25
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f165,f80,f178,f172])).

fof(f172,plain,
    ( spl8_22
  <=> sP7(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f165,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_tarski(sK1)))
    | sP7(sK2)
    | ~ spl8_0 ),
    inference(resolution,[],[f73,f81])).

fof(f160,plain,
    ( ~ spl8_21
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f151,f108,f157])).

fof(f157,plain,
    ( spl8_21
  <=> ~ sP6(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f151,plain,
    ( ~ sP6(k1_tarski(sK1),sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f72,f109])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP6(X1,X0) ) ),
    inference(general_splitting,[],[f58,f71_D])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP6(X1,X0) ) ),
    inference(cnf_transformation,[],[f71_D])).

fof(f71_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP6(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t66_funct_2.p',reflexivity_r2_relset_1)).

fof(f159,plain,
    ( ~ spl8_21
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f150,f80,f157])).

fof(f150,plain,
    ( ~ sP6(k1_tarski(sK1),sK0)
    | ~ spl8_0 ),
    inference(resolution,[],[f72,f81])).

fof(f147,plain,
    ( spl8_18
    | spl8_16
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f126,f108,f138,f145])).

fof(f126,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl8_8 ),
    inference(resolution,[],[f69,f109])).

fof(f140,plain,
    ( spl8_14
    | spl8_16
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f125,f80,f138,f132])).

fof(f125,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl8_0 ),
    inference(resolution,[],[f69,f81])).

fof(f124,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f48,f122])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X2,X0,k1_tarski(X1))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X2,X0,k1_tarski(X1))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X2,X0,k1_tarski(X1))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t66_funct_2.p',t66_funct_2)).

fof(f117,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f49,f115])).

fof(f49,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f110,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f50,f108])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f103,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f51,f101])).

fof(f51,plain,(
    ~ r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f52,f94])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f53,f87])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f54,f80])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
