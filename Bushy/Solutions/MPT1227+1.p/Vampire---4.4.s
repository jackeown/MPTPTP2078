%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t36_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:28 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  510 (1627 expanded)
%              Number of leaves         :  138 ( 663 expanded)
%              Depth                    :   12
%              Number of atoms          : 1388 (4297 expanded)
%              Number of equality atoms :  152 ( 462 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1680,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f108,f115,f122,f129,f136,f143,f150,f157,f165,f192,f199,f221,f234,f244,f254,f259,f272,f283,f294,f305,f321,f337,f347,f352,f363,f393,f403,f418,f422,f448,f458,f474,f483,f502,f512,f519,f534,f542,f558,f577,f587,f595,f604,f611,f623,f636,f659,f667,f674,f716,f723,f731,f765,f786,f803,f820,f829,f846,f863,f880,f893,f902,f919,f980,f990,f1000,f1014,f1028,f1096,f1104,f1112,f1145,f1202,f1209,f1229,f1249,f1261,f1272,f1286,f1295,f1307,f1321,f1333,f1357,f1364,f1439,f1446,f1468,f1476,f1483,f1491,f1541,f1550,f1557,f1565,f1654,f1668,f1679])).

fof(f1679,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_16
    | spl5_81 ),
    inference(avatar_contradiction_clause,[],[f1678])).

fof(f1678,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_81 ),
    inference(subsumption_resolution,[],[f1677,f511])).

fof(f511,plain,
    ( ~ v4_pre_topc(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f510])).

fof(f510,plain,
    ( spl5_81
  <=> ~ v4_pre_topc(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f1677,plain,
    ( v4_pre_topc(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f1674,f156])).

fof(f156,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl5_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1674,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(resolution,[],[f1671,f135])).

fof(f135,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl5_10
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f1671,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k2_xboole_0(sK1,X0),sK0) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f1669,f149])).

fof(f149,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl5_14
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f1669,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k2_xboole_0(sK1,X0),sK0) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(resolution,[],[f613,f128])).

fof(f128,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_8
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f613,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X1,sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k2_xboole_0(X1,X0),sK0) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f612,f107])).

fof(f107,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f612,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X1,sK0)
        | ~ l1_pre_topc(sK0)
        | v4_pre_topc(k2_xboole_0(X1,X0),sK0) )
    | ~ spl5_0 ),
    inference(resolution,[],[f84,f100])).

fof(f100,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',fc5_tops_1)).

fof(f1668,plain,
    ( ~ spl5_223
    | spl5_224
    | spl5_57
    | ~ spl5_134 ),
    inference(avatar_split_clause,[],[f895,f885,f355,f1666,f1660])).

fof(f1660,plain,
    ( spl5_223
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(k2_xboole_0(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_223])])).

fof(f1666,plain,
    ( spl5_224
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(k2_xboole_0(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_224])])).

fof(f355,plain,
    ( spl5_57
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f885,plain,
    ( spl5_134
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(k2_xboole_0(sK1,sK2)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f895,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k2_xboole_0(sK1,sK2)))))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(k2_xboole_0(sK1,sK2)))))
    | ~ spl5_57
    | ~ spl5_134 ),
    inference(subsumption_resolution,[],[f894,f356])).

fof(f356,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f355])).

fof(f894,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k2_xboole_0(sK1,sK2)))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(k2_xboole_0(sK1,sK2)))))
    | ~ spl5_134 ),
    inference(resolution,[],[f886,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f176,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',t2_subset)).

fof(f176,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f81,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',antisymmetry_r2_hidden)).

fof(f886,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(k2_xboole_0(sK1,sK2)))),u1_struct_0(sK0))
    | ~ spl5_134 ),
    inference(avatar_component_clause,[],[f885])).

fof(f1654,plain,
    ( spl5_220
    | ~ spl5_44
    | ~ spl5_78
    | ~ spl5_98
    | ~ spl5_218 ),
    inference(avatar_split_clause,[],[f1616,f1563,f609,f500,f292,f1652])).

fof(f1652,plain,
    ( spl5_220
  <=> k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),o_0_0_xboole_0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_220])])).

fof(f292,plain,
    ( spl5_44
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f500,plain,
    ( spl5_78
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f609,plain,
    ( spl5_98
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f1563,plain,
    ( spl5_218
  <=> k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_218])])).

fof(f1616,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),o_0_0_xboole_0) = k2_xboole_0(sK1,sK2)
    | ~ spl5_44
    | ~ spl5_78
    | ~ spl5_98
    | ~ spl5_218 ),
    inference(forward_demodulation,[],[f1615,f1564])).

fof(f1564,plain,
    ( k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2)
    | ~ spl5_218 ),
    inference(avatar_component_clause,[],[f1563])).

fof(f1615,plain,
    ( k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,k2_xboole_0(sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),o_0_0_xboole_0)
    | ~ spl5_44
    | ~ spl5_78
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f1588,f501])).

fof(f501,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f500])).

fof(f1588,plain,
    ( k4_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2),o_0_0_xboole_0) = k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl5_44
    | ~ spl5_98 ),
    inference(resolution,[],[f1340,f293])).

fof(f293,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f292])).

fof(f1340,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),X0,o_0_0_xboole_0) = k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,X0) )
    | ~ spl5_98 ),
    inference(resolution,[],[f610,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',commutativity_k4_subset_1)).

fof(f610,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_98 ),
    inference(avatar_component_clause,[],[f609])).

fof(f1565,plain,
    ( spl5_218
    | ~ spl5_44
    | ~ spl5_78
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f1521,f609,f500,f292,f1563])).

fof(f1521,plain,
    ( k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2)
    | ~ spl5_44
    | ~ spl5_78
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f1495,f501])).

fof(f1495,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl5_44
    | ~ spl5_98 ),
    inference(resolution,[],[f1350,f293])).

fof(f1350,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,X1) = X1 )
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f1341,f166])).

fof(f166,plain,(
    ! [X1] : k2_xboole_0(o_0_0_xboole_0,X1) = X1 ),
    inference(superposition,[],[f78,f93])).

fof(f93,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f74,f73])).

fof(f73,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',d2_xboole_0)).

fof(f74,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',t1_boole)).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',commutativity_k2_xboole_0)).

fof(f1341,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,X1) = k2_xboole_0(o_0_0_xboole_0,X1) )
    | ~ spl5_98 ),
    inference(resolution,[],[f610,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',redefinition_k4_subset_1)).

fof(f1557,plain,
    ( spl5_216
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f1400,f609,f1555])).

fof(f1555,plain,
    ( spl5_216
  <=> k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) = sK3(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_216])])).

fof(f1400,plain,
    ( k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) = sK3(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f1373,f1349])).

fof(f1349,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK3(k1_zfmisc_1(u1_struct_0(sK0))),o_0_0_xboole_0) = sK3(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f1339,f93])).

fof(f1339,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK3(k1_zfmisc_1(u1_struct_0(sK0))),o_0_0_xboole_0) = k2_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK0))),o_0_0_xboole_0)
    | ~ spl5_98 ),
    inference(resolution,[],[f610,f372])).

fof(f372,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
      | k4_subset_1(X9,sK3(k1_zfmisc_1(X9)),X8) = k2_xboole_0(sK3(k1_zfmisc_1(X9)),X8) ) ),
    inference(resolution,[],[f88,f76])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',existence_m1_subset_1)).

fof(f1373,plain,
    ( k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) = k4_subset_1(u1_struct_0(sK0),sK3(k1_zfmisc_1(u1_struct_0(sK0))),o_0_0_xboole_0)
    | ~ spl5_98 ),
    inference(resolution,[],[f482,f610])).

fof(f482,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
      | k4_subset_1(X9,X8,sK3(k1_zfmisc_1(X9))) = k4_subset_1(X9,sK3(k1_zfmisc_1(X9)),X8) ) ),
    inference(resolution,[],[f89,f76])).

fof(f1550,plain,
    ( spl5_214
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f1349,f609,f1548])).

fof(f1548,plain,
    ( spl5_214
  <=> k4_subset_1(u1_struct_0(sK0),sK3(k1_zfmisc_1(u1_struct_0(sK0))),o_0_0_xboole_0) = sK3(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_214])])).

fof(f1541,plain,
    ( spl5_212
    | ~ spl5_14
    | ~ spl5_202 ),
    inference(avatar_split_clause,[],[f1460,f1444,f148,f1539])).

fof(f1539,plain,
    ( spl5_212
  <=> m1_subset_1(k2_xboole_0(sK1,k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_212])])).

fof(f1444,plain,
    ( spl5_202
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_202])])).

fof(f1460,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_202 ),
    inference(forward_demodulation,[],[f1451,f1450])).

fof(f1450,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK1)) = k2_xboole_0(sK1,k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK1))
    | ~ spl5_14
    | ~ spl5_202 ),
    inference(resolution,[],[f1445,f370])).

fof(f370,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X6) = k2_xboole_0(sK1,X6) )
    | ~ spl5_14 ),
    inference(resolution,[],[f88,f149])).

fof(f1445,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_202 ),
    inference(avatar_component_clause,[],[f1444])).

fof(f1451,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_202 ),
    inference(resolution,[],[f1445,f256])).

fof(f256,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_14 ),
    inference(resolution,[],[f87,f149])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',dt_k4_subset_1)).

fof(f1491,plain,
    ( spl5_210
    | ~ spl5_200
    | ~ spl5_208 ),
    inference(avatar_split_clause,[],[f1484,f1481,f1437,f1489])).

fof(f1489,plain,
    ( spl5_210
  <=> k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_210])])).

fof(f1437,plain,
    ( spl5_200
  <=> k4_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_200])])).

fof(f1481,plain,
    ( spl5_208
  <=> k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_208])])).

fof(f1484,plain,
    ( k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK1) = sK1
    | ~ spl5_200
    | ~ spl5_208 ),
    inference(forward_demodulation,[],[f1482,f1438])).

fof(f1438,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0) = sK1
    | ~ spl5_200 ),
    inference(avatar_component_clause,[],[f1437])).

fof(f1482,plain,
    ( k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0)
    | ~ spl5_208 ),
    inference(avatar_component_clause,[],[f1481])).

fof(f1483,plain,
    ( spl5_208
    | ~ spl5_14
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f1335,f609,f148,f1481])).

fof(f1335,plain,
    ( k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0)
    | ~ spl5_14
    | ~ spl5_98 ),
    inference(resolution,[],[f610,f480])).

fof(f480,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),X6,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,X6) )
    | ~ spl5_14 ),
    inference(resolution,[],[f89,f149])).

fof(f1476,plain,
    ( spl5_206
    | ~ spl5_198
    | ~ spl5_204 ),
    inference(avatar_split_clause,[],[f1469,f1466,f1362,f1474])).

fof(f1474,plain,
    ( spl5_206
  <=> k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_206])])).

fof(f1362,plain,
    ( spl5_198
  <=> k4_subset_1(u1_struct_0(sK0),sK2,o_0_0_xboole_0) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_198])])).

fof(f1466,plain,
    ( spl5_204
  <=> k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).

fof(f1469,plain,
    ( k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK2) = sK2
    | ~ spl5_198
    | ~ spl5_204 ),
    inference(forward_demodulation,[],[f1467,f1363])).

fof(f1363,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,o_0_0_xboole_0) = sK2
    | ~ spl5_198 ),
    inference(avatar_component_clause,[],[f1362])).

fof(f1467,plain,
    ( k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,o_0_0_xboole_0)
    | ~ spl5_204 ),
    inference(avatar_component_clause,[],[f1466])).

fof(f1468,plain,
    ( spl5_204
    | ~ spl5_16
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f1334,f609,f155,f1466])).

fof(f1334,plain,
    ( k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,o_0_0_xboole_0)
    | ~ spl5_16
    | ~ spl5_98 ),
    inference(resolution,[],[f610,f481])).

fof(f481,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),X7,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,X7) )
    | ~ spl5_16 ),
    inference(resolution,[],[f89,f156])).

fof(f1446,plain,
    ( spl5_202
    | ~ spl5_14
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f1348,f609,f148,f1444])).

fof(f1348,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f1338,f1335])).

fof(f1338,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_98 ),
    inference(resolution,[],[f610,f256])).

fof(f1439,plain,
    ( spl5_200
    | ~ spl5_14
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f1347,f609,f148,f1437])).

fof(f1347,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0) = sK1
    | ~ spl5_14
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f1337,f93])).

fof(f1337,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0) = k2_xboole_0(sK1,o_0_0_xboole_0)
    | ~ spl5_14
    | ~ spl5_98 ),
    inference(resolution,[],[f610,f370])).

fof(f1364,plain,
    ( spl5_198
    | ~ spl5_16
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f1346,f609,f155,f1362])).

fof(f1346,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,o_0_0_xboole_0) = sK2
    | ~ spl5_16
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f1336,f93])).

fof(f1336,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,o_0_0_xboole_0) = k2_xboole_0(sK2,o_0_0_xboole_0)
    | ~ spl5_16
    | ~ spl5_98 ),
    inference(resolution,[],[f610,f371])).

fof(f371,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK2,X7) = k2_xboole_0(sK2,X7) )
    | ~ spl5_16 ),
    inference(resolution,[],[f88,f156])).

fof(f1357,plain,
    ( spl5_196
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f1344,f609,f1355])).

fof(f1355,plain,
    ( spl5_196
  <=> k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_196])])).

fof(f1344,plain,
    ( k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_98 ),
    inference(resolution,[],[f610,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X1) = X1 ) ),
    inference(condensation,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',idempotence_k4_subset_1)).

fof(f1333,plain,
    ( spl5_98
    | ~ spl5_126
    | ~ spl5_194 ),
    inference(avatar_split_clause,[],[f1326,f1319,f827,f609])).

fof(f827,plain,
    ( spl5_126
  <=> m1_subset_1(k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f1319,plain,
    ( spl5_194
  <=> o_0_0_xboole_0 = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).

fof(f1326,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_126
    | ~ spl5_194 ),
    inference(superposition,[],[f828,f1320])).

fof(f1320,plain,
    ( o_0_0_xboole_0 = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl5_194 ),
    inference(avatar_component_clause,[],[f1319])).

fof(f828,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_126 ),
    inference(avatar_component_clause,[],[f827])).

fof(f1321,plain,
    ( spl5_194
    | ~ spl5_146
    | ~ spl5_148
    | ~ spl5_190 ),
    inference(avatar_split_clause,[],[f1312,f1302,f998,f988,f1319])).

fof(f988,plain,
    ( spl5_146
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f998,plain,
    ( spl5_148
  <=> o_0_0_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).

fof(f1302,plain,
    ( spl5_190
  <=> v1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_190])])).

fof(f1312,plain,
    ( o_0_0_xboole_0 = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl5_146
    | ~ spl5_148
    | ~ spl5_190 ),
    inference(forward_demodulation,[],[f1308,f999])).

fof(f999,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_148 ),
    inference(avatar_component_clause,[],[f998])).

fof(f1308,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_146
    | ~ spl5_190 ),
    inference(resolution,[],[f1303,f992])).

fof(f992,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) = X2 )
    | ~ spl5_146 ),
    inference(resolution,[],[f989,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',t8_boole)).

fof(f989,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl5_146 ),
    inference(avatar_component_clause,[],[f988])).

fof(f1303,plain,
    ( v1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))
    | ~ spl5_190 ),
    inference(avatar_component_clause,[],[f1302])).

fof(f1307,plain,
    ( spl5_190
    | spl5_192
    | ~ spl5_126 ),
    inference(avatar_split_clause,[],[f835,f827,f1305,f1302])).

fof(f1305,plain,
    ( spl5_192
  <=> ! [X2] :
        ( m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_192])])).

fof(f835,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,u1_struct_0(sK0))
        | v1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(X2,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) )
    | ~ spl5_126 ),
    inference(resolution,[],[f828,f182])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f85,f81])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',t4_subset)).

fof(f1295,plain,
    ( spl5_188
    | ~ spl5_184 ),
    inference(avatar_split_clause,[],[f1287,f1270,f1293])).

fof(f1293,plain,
    ( spl5_188
  <=> m1_subset_1(sK3(k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_188])])).

fof(f1270,plain,
    ( spl5_184
  <=> ! [X2] :
        ( m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_184])])).

fof(f1287,plain,
    ( m1_subset_1(sK3(k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0))
    | ~ spl5_184 ),
    inference(resolution,[],[f1271,f76])).

fof(f1271,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)))
        | m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl5_184 ),
    inference(avatar_component_clause,[],[f1270])).

fof(f1286,plain,
    ( spl5_186
    | ~ spl5_146
    | ~ spl5_148
    | ~ spl5_182 ),
    inference(avatar_split_clause,[],[f1277,f1267,f998,f988,f1284])).

fof(f1284,plain,
    ( spl5_186
  <=> o_0_0_xboole_0 = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_186])])).

fof(f1267,plain,
    ( spl5_182
  <=> v1_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_182])])).

fof(f1277,plain,
    ( o_0_0_xboole_0 = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl5_146
    | ~ spl5_148
    | ~ spl5_182 ),
    inference(forward_demodulation,[],[f1273,f999])).

fof(f1273,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_146
    | ~ spl5_182 ),
    inference(resolution,[],[f1268,f992])).

fof(f1268,plain,
    ( v1_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)))
    | ~ spl5_182 ),
    inference(avatar_component_clause,[],[f1267])).

fof(f1272,plain,
    ( spl5_182
    | spl5_184
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f547,f540,f1270,f1267])).

fof(f540,plain,
    ( spl5_86
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f547,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,u1_struct_0(sK0))
        | v1_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(X2,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))) )
    | ~ spl5_86 ),
    inference(resolution,[],[f541,f182])).

fof(f541,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_86 ),
    inference(avatar_component_clause,[],[f540])).

fof(f1261,plain,
    ( spl5_178
    | spl5_180
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f326,f292,f1259,f1256])).

fof(f1256,plain,
    ( spl5_178
  <=> v1_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).

fof(f1259,plain,
    ( spl5_180
  <=> ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_180])])).

fof(f326,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,sK2))
        | ~ m1_subset_1(X0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) )
    | ~ spl5_44 ),
    inference(resolution,[],[f182,f293])).

fof(f1249,plain,
    ( spl5_176
    | ~ spl5_14
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f306,f303,f148,f1247])).

fof(f1247,plain,
    ( spl5_176
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_176])])).

fof(f303,plain,
    ( spl5_46
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f306,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_46 ),
    inference(resolution,[],[f304,f256])).

fof(f304,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f303])).

fof(f1229,plain,
    ( spl5_174
    | ~ spl5_14
    | ~ spl5_130 ),
    inference(avatar_split_clause,[],[f873,f861,f148,f1227])).

fof(f1227,plain,
    ( spl5_174
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_174])])).

fof(f861,plain,
    ( spl5_130
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).

fof(f873,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_130 ),
    inference(forward_demodulation,[],[f866,f865])).

fof(f865,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))))
    | ~ spl5_14
    | ~ spl5_130 ),
    inference(resolution,[],[f862,f370])).

fof(f862,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_130 ),
    inference(avatar_component_clause,[],[f861])).

fof(f866,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_130 ),
    inference(resolution,[],[f862,f256])).

fof(f1209,plain,
    ( spl5_172
    | ~ spl5_14
    | ~ spl5_110 ),
    inference(avatar_split_clause,[],[f684,f672,f148,f1207])).

fof(f1207,plain,
    ( spl5_172
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_172])])).

fof(f672,plain,
    ( spl5_110
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f684,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_110 ),
    inference(forward_demodulation,[],[f677,f676])).

fof(f676,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)))))
    | ~ spl5_14
    | ~ spl5_110 ),
    inference(resolution,[],[f673,f370])).

fof(f673,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_110 ),
    inference(avatar_component_clause,[],[f672])).

fof(f677,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_110 ),
    inference(resolution,[],[f673,f256])).

fof(f1202,plain,
    ( spl5_166
    | ~ spl5_169
    | spl5_170
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f701,f420,f1200,f1194,f1188])).

fof(f1188,plain,
    ( spl5_166
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_166])])).

fof(f1194,plain,
    ( spl5_169
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).

fof(f1200,plain,
    ( spl5_170
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_170])])).

fof(f420,plain,
    ( spl5_68
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(u1_struct_0(sK0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f701,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK2))))
    | v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ spl5_68 ),
    inference(resolution,[],[f686,f421])).

fof(f421,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(u1_struct_0(sK0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f420])).

fof(f686,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK3(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK3(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f333,f76])).

fof(f333,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,sK3(k1_zfmisc_1(X9)))
      | v1_xboole_0(sK3(k1_zfmisc_1(X9)))
      | m1_subset_1(X8,X9) ) ),
    inference(resolution,[],[f182,f76])).

fof(f1145,plain,
    ( spl5_160
    | ~ spl5_163
    | spl5_164
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f700,f361,f1143,f1137,f1131])).

fof(f1131,plain,
    ( spl5_160
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).

fof(f1137,plain,
    ( spl5_163
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).

fof(f1143,plain,
    ( spl5_164
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_164])])).

fof(f361,plain,
    ( spl5_58
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(u1_struct_0(sK0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f700,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK1))))
    | v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK1))))
    | ~ spl5_58 ),
    inference(resolution,[],[f686,f362])).

fof(f362,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(u1_struct_0(sK0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f361])).

fof(f1112,plain,
    ( spl5_158
    | ~ spl5_16
    | ~ spl5_44
    | ~ spl5_78
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f1069,f818,f500,f292,f155,f1110])).

fof(f1110,plain,
    ( spl5_158
  <=> k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK2) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_158])])).

fof(f818,plain,
    ( spl5_124
  <=> k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f1069,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK2) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl5_16
    | ~ spl5_44
    | ~ spl5_78
    | ~ spl5_124 ),
    inference(forward_demodulation,[],[f1068,f819])).

fof(f819,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl5_124 ),
    inference(avatar_component_clause,[],[f818])).

fof(f1068,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK1,sK2))
    | ~ spl5_16
    | ~ spl5_44
    | ~ spl5_78 ),
    inference(forward_demodulation,[],[f1046,f501])).

fof(f1046,plain,
    ( k4_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl5_16
    | ~ spl5_44 ),
    inference(resolution,[],[f481,f293])).

fof(f1104,plain,
    ( spl5_156
    | ~ spl5_16
    | ~ spl5_114 ),
    inference(avatar_split_clause,[],[f1089,f721,f155,f1102])).

fof(f1102,plain,
    ( spl5_156
  <=> k4_subset_1(u1_struct_0(sK0),sK3(k1_zfmisc_1(u1_struct_0(sK0))),sK2) = k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_156])])).

fof(f721,plain,
    ( spl5_114
  <=> k4_subset_1(u1_struct_0(sK0),sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f1089,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK3(k1_zfmisc_1(u1_struct_0(sK0))),sK2) = k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_16
    | ~ spl5_114 ),
    inference(forward_demodulation,[],[f1066,f722])).

fof(f722,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_114 ),
    inference(avatar_component_clause,[],[f721])).

fof(f1066,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) = k4_subset_1(u1_struct_0(sK0),sK3(k1_zfmisc_1(u1_struct_0(sK0))),sK2)
    | ~ spl5_16 ),
    inference(resolution,[],[f481,f76])).

fof(f1096,plain,
    ( spl5_154
    | ~ spl5_14
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f973,f714,f148,f1094])).

fof(f1094,plain,
    ( spl5_154
  <=> k4_subset_1(u1_struct_0(sK0),sK3(k1_zfmisc_1(u1_struct_0(sK0))),sK1) = k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f714,plain,
    ( spl5_112
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f973,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK3(k1_zfmisc_1(u1_struct_0(sK0))),sK1) = k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_14
    | ~ spl5_112 ),
    inference(forward_demodulation,[],[f950,f715])).

fof(f715,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_112 ),
    inference(avatar_component_clause,[],[f714])).

fof(f950,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) = k4_subset_1(u1_struct_0(sK0),sK3(k1_zfmisc_1(u1_struct_0(sK0))),sK1)
    | ~ spl5_14 ),
    inference(resolution,[],[f480,f76])).

fof(f1028,plain,
    ( spl5_152
    | ~ spl5_148 ),
    inference(avatar_split_clause,[],[f1005,f998,f1026])).

fof(f1026,plain,
    ( spl5_152
  <=> k4_subset_1(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_152])])).

fof(f1005,plain,
    ( k4_subset_1(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_148 ),
    inference(superposition,[],[f183,f999])).

fof(f183,plain,(
    ! [X0] : k4_subset_1(X0,sK3(k1_zfmisc_1(X0)),sK3(k1_zfmisc_1(X0))) = sK3(k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f92,f76])).

fof(f1014,plain,
    ( spl5_150
    | ~ spl5_148 ),
    inference(avatar_split_clause,[],[f1007,f998,f1012])).

fof(f1012,plain,
    ( spl5_150
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).

fof(f1007,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_148 ),
    inference(superposition,[],[f76,f999])).

fof(f1000,plain,
    ( spl5_148
    | ~ spl5_146 ),
    inference(avatar_split_clause,[],[f993,f988,f998])).

fof(f993,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_146 ),
    inference(resolution,[],[f989,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f75,f73])).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',t6_boole)).

fof(f990,plain,
    ( spl5_144
    | spl5_146
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f690,f113,f988,f982])).

fof(f982,plain,
    ( spl5_144
  <=> ! [X1] : ~ r2_hidden(X1,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).

fof(f113,plain,
    ( spl5_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f690,plain,
    ( ! [X1] :
        ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
        | ~ r2_hidden(X1,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f686,f179])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f90,f114])).

fof(f114,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',t5_subset)).

fof(f980,plain,
    ( spl5_142
    | ~ spl5_14
    | ~ spl5_44
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f953,f500,f292,f148,f978])).

fof(f978,plain,
    ( spl5_142
  <=> k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f953,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl5_14
    | ~ spl5_44
    | ~ spl5_78 ),
    inference(forward_demodulation,[],[f952,f501])).

fof(f952,plain,
    ( k4_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) = k2_xboole_0(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f930,f487])).

fof(f487,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k2_xboole_0(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(resolution,[],[f370,f293])).

fof(f930,plain,
    ( k4_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(resolution,[],[f480,f293])).

fof(f919,plain,
    ( spl5_140
    | ~ spl5_14
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f813,f801,f148,f917])).

fof(f917,plain,
    ( spl5_140
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f801,plain,
    ( spl5_122
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f813,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f806,f805])).

fof(f805,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl5_14
    | ~ spl5_122 ),
    inference(resolution,[],[f802,f370])).

fof(f802,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_122 ),
    inference(avatar_component_clause,[],[f801])).

fof(f806,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_122 ),
    inference(resolution,[],[f802,f256])).

fof(f902,plain,
    ( spl5_138
    | ~ spl5_14
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f775,f763,f148,f900])).

fof(f900,plain,
    ( spl5_138
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f763,plain,
    ( spl5_118
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f775,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f768,f767])).

fof(f767,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl5_14
    | ~ spl5_118 ),
    inference(resolution,[],[f764,f370])).

fof(f764,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_118 ),
    inference(avatar_component_clause,[],[f763])).

fof(f768,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_118 ),
    inference(resolution,[],[f764,f256])).

fof(f893,plain,
    ( spl5_134
    | spl5_136
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f699,f575,f891,f885])).

fof(f891,plain,
    ( spl5_136
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f575,plain,
    ( spl5_92
  <=> ! [X2] :
        ( m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k2_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f699,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k2_xboole_0(sK1,sK2))))
    | m1_subset_1(sK3(sK3(k1_zfmisc_1(k2_xboole_0(sK1,sK2)))),u1_struct_0(sK0))
    | ~ spl5_92 ),
    inference(resolution,[],[f686,f576])).

fof(f576,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k2_xboole_0(sK1,sK2))
        | m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl5_92 ),
    inference(avatar_component_clause,[],[f575])).

fof(f880,plain,
    ( ~ spl5_133
    | spl5_26
    | spl5_90
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f527,f517,f572,f213,f878])).

fof(f878,plain,
    ( spl5_133
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_133])])).

fof(f213,plain,
    ( spl5_26
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f572,plain,
    ( spl5_90
  <=> v1_xboole_0(k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f517,plain,
    ( spl5_82
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f527,plain,
    ( v1_xboole_0(k2_xboole_0(sK1,sK2))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))
    | ~ spl5_82 ),
    inference(resolution,[],[f518,f178])).

fof(f518,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f517])).

fof(f863,plain,
    ( spl5_130
    | ~ spl5_14
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f856,f844,f148,f861])).

fof(f844,plain,
    ( spl5_128
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f856,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_128 ),
    inference(forward_demodulation,[],[f849,f848])).

fof(f848,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))))
    | ~ spl5_14
    | ~ spl5_128 ),
    inference(resolution,[],[f845,f370])).

fof(f845,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_128 ),
    inference(avatar_component_clause,[],[f844])).

fof(f849,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_128 ),
    inference(resolution,[],[f845,f256])).

fof(f846,plain,
    ( spl5_128
    | ~ spl5_14
    | ~ spl5_126 ),
    inference(avatar_split_clause,[],[f839,f827,f148,f844])).

fof(f839,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_126 ),
    inference(forward_demodulation,[],[f832,f831])).

fof(f831,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))
    | ~ spl5_14
    | ~ spl5_126 ),
    inference(resolution,[],[f828,f370])).

fof(f832,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_126 ),
    inference(resolution,[],[f828,f256])).

fof(f829,plain,
    ( spl5_126
    | ~ spl5_16
    | ~ spl5_82
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f822,f818,f517,f155,f827])).

fof(f822,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16
    | ~ spl5_82
    | ~ spl5_124 ),
    inference(subsumption_resolution,[],[f821,f518])).

fof(f821,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16
    | ~ spl5_124 ),
    inference(superposition,[],[f257,f819])).

fof(f257,plain,
    ( ! [X3] :
        ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_16 ),
    inference(resolution,[],[f87,f156])).

fof(f820,plain,
    ( spl5_124
    | ~ spl5_16
    | ~ spl5_44
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f647,f500,f292,f155,f818])).

fof(f647,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl5_16
    | ~ spl5_44
    | ~ spl5_78 ),
    inference(forward_demodulation,[],[f637,f501])).

fof(f637,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k2_xboole_0(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl5_16
    | ~ spl5_44 ),
    inference(resolution,[],[f371,f293])).

fof(f803,plain,
    ( spl5_122
    | ~ spl5_14
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f796,f784,f148,f801])).

fof(f784,plain,
    ( spl5_120
  <=> m1_subset_1(k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f796,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_120 ),
    inference(forward_demodulation,[],[f789,f788])).

fof(f788,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_14
    | ~ spl5_120 ),
    inference(resolution,[],[f785,f370])).

fof(f785,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_120 ),
    inference(avatar_component_clause,[],[f784])).

fof(f789,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_120 ),
    inference(resolution,[],[f785,f256])).

fof(f786,plain,
    ( spl5_120
    | ~ spl5_16
    | ~ spl5_114 ),
    inference(avatar_split_clause,[],[f779,f721,f155,f784])).

fof(f779,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16
    | ~ spl5_114 ),
    inference(subsumption_resolution,[],[f778,f76])).

fof(f778,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16
    | ~ spl5_114 ),
    inference(superposition,[],[f257,f722])).

fof(f765,plain,
    ( spl5_118
    | ~ spl5_14
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f741,f729,f148,f763])).

fof(f729,plain,
    ( spl5_116
  <=> m1_subset_1(k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f741,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_116 ),
    inference(forward_demodulation,[],[f734,f733])).

fof(f733,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_14
    | ~ spl5_116 ),
    inference(resolution,[],[f730,f370])).

fof(f730,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_116 ),
    inference(avatar_component_clause,[],[f729])).

fof(f734,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_116 ),
    inference(resolution,[],[f730,f256])).

fof(f731,plain,
    ( spl5_116
    | ~ spl5_46
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f724,f714,f303,f729])).

fof(f724,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_46
    | ~ spl5_112 ),
    inference(superposition,[],[f304,f715])).

fof(f723,plain,
    ( spl5_114
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f646,f155,f721])).

fof(f646,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_xboole_0(sK2,sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_16 ),
    inference(resolution,[],[f371,f76])).

fof(f716,plain,
    ( spl5_112
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f493,f148,f714])).

fof(f493,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_xboole_0(sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_14 ),
    inference(resolution,[],[f370,f76])).

fof(f674,plain,
    ( spl5_110
    | ~ spl5_14
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f567,f556,f148,f672])).

fof(f556,plain,
    ( spl5_88
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f567,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_88 ),
    inference(forward_demodulation,[],[f560,f559])).

fof(f559,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))))
    | ~ spl5_14
    | ~ spl5_88 ),
    inference(resolution,[],[f557,f370])).

fof(f557,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f556])).

fof(f560,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_88 ),
    inference(resolution,[],[f557,f256])).

fof(f667,plain,
    ( spl5_108
    | ~ spl5_14
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f520,f517,f148,f665])).

fof(f665,plain,
    ( spl5_108
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f520,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl5_14
    | ~ spl5_82 ),
    inference(resolution,[],[f518,f370])).

fof(f659,plain,
    ( spl5_106
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f651,f155,f148,f657])).

fof(f657,plain,
    ( spl5_106
  <=> k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f651,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f644,f78])).

fof(f644,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(resolution,[],[f371,f149])).

fof(f636,plain,
    ( ~ spl5_103
    | spl5_104
    | spl5_57
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f615,f593,f355,f634,f628])).

fof(f628,plain,
    ( spl5_103
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f634,plain,
    ( spl5_104
  <=> v1_xboole_0(sK3(k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f593,plain,
    ( spl5_96
  <=> m1_subset_1(sK3(k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f615,plain,
    ( v1_xboole_0(sK3(k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(k2_xboole_0(sK1,sK2)))
    | ~ spl5_57
    | ~ spl5_96 ),
    inference(subsumption_resolution,[],[f614,f356])).

fof(f614,plain,
    ( v1_xboole_0(sK3(k2_xboole_0(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK3(k2_xboole_0(sK1,sK2)))
    | ~ spl5_96 ),
    inference(resolution,[],[f594,f178])).

fof(f594,plain,
    ( m1_subset_1(sK3(k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ spl5_96 ),
    inference(avatar_component_clause,[],[f593])).

fof(f623,plain,
    ( spl5_100
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f526,f517,f621])).

fof(f621,plain,
    ( spl5_100
  <=> k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f526,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2)
    | ~ spl5_82 ),
    inference(resolution,[],[f518,f92])).

fof(f611,plain,
    ( spl5_98
    | ~ spl5_82
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f599,f585,f517,f609])).

fof(f585,plain,
    ( spl5_94
  <=> o_0_0_xboole_0 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f599,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_82
    | ~ spl5_94 ),
    inference(superposition,[],[f518,f586])).

fof(f586,plain,
    ( o_0_0_xboole_0 = k2_xboole_0(sK1,sK2)
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f585])).

fof(f604,plain,
    ( ~ spl5_61
    | spl5_81
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f600,f585,f510,f388])).

fof(f388,plain,
    ( spl5_61
  <=> ~ v4_pre_topc(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f600,plain,
    ( ~ v4_pre_topc(o_0_0_xboole_0,sK0)
    | ~ spl5_81
    | ~ spl5_94 ),
    inference(superposition,[],[f511,f586])).

fof(f595,plain,
    ( spl5_96
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f588,f575,f593])).

fof(f588,plain,
    ( m1_subset_1(sK3(k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ spl5_92 ),
    inference(resolution,[],[f576,f76])).

fof(f587,plain,
    ( spl5_94
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f580,f572,f585])).

fof(f580,plain,
    ( o_0_0_xboole_0 = k2_xboole_0(sK1,sK2)
    | ~ spl5_90 ),
    inference(resolution,[],[f573,f94])).

fof(f573,plain,
    ( v1_xboole_0(k2_xboole_0(sK1,sK2))
    | ~ spl5_90 ),
    inference(avatar_component_clause,[],[f572])).

fof(f577,plain,
    ( spl5_90
    | spl5_92
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f524,f517,f575,f572])).

fof(f524,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,u1_struct_0(sK0))
        | v1_xboole_0(k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X2,k2_xboole_0(sK1,sK2)) )
    | ~ spl5_82 ),
    inference(resolution,[],[f518,f182])).

fof(f558,plain,
    ( spl5_88
    | ~ spl5_14
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f551,f540,f148,f556])).

fof(f551,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_86 ),
    inference(forward_demodulation,[],[f544,f543])).

fof(f543,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)))
    | ~ spl5_14
    | ~ spl5_86 ),
    inference(resolution,[],[f541,f370])).

fof(f544,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_86 ),
    inference(resolution,[],[f541,f256])).

fof(f542,plain,
    ( spl5_86
    | ~ spl5_14
    | ~ spl5_82
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f535,f532,f517,f148,f540])).

fof(f532,plain,
    ( spl5_84
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f535,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_82
    | ~ spl5_84 ),
    inference(forward_demodulation,[],[f533,f520])).

fof(f533,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f532])).

fof(f534,plain,
    ( spl5_84
    | ~ spl5_48
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f503,f500,f319,f532])).

fof(f319,plain,
    ( spl5_48
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f503,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_48
    | ~ spl5_78 ),
    inference(superposition,[],[f320,f501])).

fof(f320,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f319])).

fof(f519,plain,
    ( spl5_82
    | ~ spl5_44
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f504,f500,f292,f517])).

fof(f504,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_44
    | ~ spl5_78 ),
    inference(superposition,[],[f293,f501])).

fof(f512,plain,
    ( ~ spl5_81
    | spl5_19
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f505,f500,f163,f510])).

fof(f163,plain,
    ( spl5_19
  <=> ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f505,plain,
    ( ~ v4_pre_topc(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_19
    | ~ spl5_78 ),
    inference(superposition,[],[f164,f501])).

fof(f164,plain,
    ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f163])).

fof(f502,plain,
    ( spl5_78
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f492,f155,f148,f500])).

fof(f492,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(resolution,[],[f370,f156])).

fof(f483,plain,
    ( spl5_56
    | spl5_58
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f404,f335,f361,f358])).

fof(f358,plain,
    ( spl5_56
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f335,plain,
    ( spl5_50
  <=> ! [X6] :
        ( m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f404,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(X0)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(sK0),X0) )
    | ~ spl5_50 ),
    inference(resolution,[],[f336,f178])).

fof(f336,plain,
    ( ! [X6] :
        ( m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,sK1) )
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f335])).

fof(f474,plain,
    ( spl5_74
    | ~ spl5_77
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f461,f420,f472,f466])).

fof(f466,plain,
    ( spl5_74
  <=> v1_xboole_0(sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f472,plain,
    ( spl5_77
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f461,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK3(sK2))
    | v1_xboole_0(sK3(sK2))
    | ~ spl5_68 ),
    inference(resolution,[],[f421,f76])).

fof(f458,plain,
    ( spl5_72
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f451,f232,f456])).

fof(f456,plain,
    ( spl5_72
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f232,plain,
    ( spl5_32
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f451,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl5_32 ),
    inference(resolution,[],[f233,f94])).

fof(f233,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f232])).

fof(f448,plain,
    ( spl5_70
    | ~ spl5_14
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f424,f401,f148,f446])).

fof(f446,plain,
    ( spl5_70
  <=> m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f401,plain,
    ( spl5_62
  <=> u1_struct_0(sK0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f424,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_62 ),
    inference(superposition,[],[f149,f402])).

fof(f402,plain,
    ( u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f401])).

fof(f422,plain,
    ( spl5_56
    | spl5_68
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f353,f350,f420,f358])).

fof(f350,plain,
    ( spl5_54
  <=> ! [X7] :
        ( m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f353,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | v1_xboole_0(X0)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(sK0),X0) )
    | ~ spl5_54 ),
    inference(resolution,[],[f351,f178])).

fof(f351,plain,
    ( ! [X7] :
        ( m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,sK2) )
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f350])).

fof(f418,plain,
    ( spl5_64
    | ~ spl5_67
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f405,f361,f416,f410])).

fof(f410,plain,
    ( spl5_64
  <=> v1_xboole_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f416,plain,
    ( spl5_67
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f405,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK3(sK1))
    | v1_xboole_0(sK3(sK1))
    | ~ spl5_58 ),
    inference(resolution,[],[f362,f76])).

fof(f403,plain,
    ( spl5_62
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f396,f358,f401])).

fof(f396,plain,
    ( u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl5_56 ),
    inference(resolution,[],[f359,f94])).

fof(f359,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f358])).

fof(f393,plain,
    ( spl5_60
    | ~ spl5_8
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f379,f345,f127,f391])).

fof(f391,plain,
    ( spl5_60
  <=> v4_pre_topc(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f345,plain,
    ( spl5_52
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f379,plain,
    ( v4_pre_topc(o_0_0_xboole_0,sK0)
    | ~ spl5_8
    | ~ spl5_52 ),
    inference(superposition,[],[f128,f346])).

fof(f346,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f345])).

fof(f363,plain,
    ( spl5_56
    | spl5_58
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f348,f335,f361,f358])).

fof(f348,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(X0)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(sK0),X0) )
    | ~ spl5_50 ),
    inference(resolution,[],[f336,f178])).

fof(f352,plain,
    ( spl5_32
    | spl5_54
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f332,f155,f350,f232])).

fof(f332,plain,
    ( ! [X7] :
        ( m1_subset_1(X7,u1_struct_0(sK0))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X7,sK2) )
    | ~ spl5_16 ),
    inference(resolution,[],[f182,f156])).

fof(f347,plain,
    ( spl5_52
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f340,f219,f345])).

fof(f219,plain,
    ( spl5_28
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f340,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl5_28 ),
    inference(resolution,[],[f220,f94])).

fof(f220,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f219])).

fof(f337,plain,
    ( spl5_28
    | spl5_50
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f331,f148,f335,f219])).

fof(f331,plain,
    ( ! [X6] :
        ( m1_subset_1(X6,u1_struct_0(sK0))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X6,sK1) )
    | ~ spl5_14 ),
    inference(resolution,[],[f182,f149])).

fof(f321,plain,
    ( spl5_48
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f295,f292,f148,f319])).

fof(f295,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(resolution,[],[f293,f256])).

fof(f305,plain,
    ( spl5_46
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f286,f148,f303])).

fof(f286,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(resolution,[],[f256,f76])).

fof(f294,plain,
    ( spl5_44
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f285,f155,f148,f292])).

fof(f285,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(resolution,[],[f256,f156])).

fof(f283,plain,
    ( spl5_42
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f275,f270,f281])).

fof(f281,plain,
    ( spl5_42
  <=> k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f270,plain,
    ( spl5_40
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f275,plain,
    ( k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_40 ),
    inference(resolution,[],[f271,f92])).

fof(f271,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f270])).

fof(f272,plain,
    ( spl5_40
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f263,f252,f270])).

fof(f252,plain,
    ( spl5_38
  <=> o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f263,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_38 ),
    inference(superposition,[],[f76,f253])).

fof(f253,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f252])).

fof(f259,plain,(
    ~ spl5_34 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl5_34 ),
    inference(resolution,[],[f237,f76])).

fof(f237,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl5_34
  <=> ! [X0] : ~ m1_subset_1(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f254,plain,
    ( spl5_38
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f247,f242,f252])).

fof(f242,plain,
    ( spl5_36
  <=> v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f247,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36 ),
    inference(resolution,[],[f243,f94])).

fof(f243,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f242])).

fof(f244,plain,
    ( spl5_34
    | spl5_36
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f181,f113,f242,f236])).

fof(f181,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
        | ~ m1_subset_1(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f180,f81])).

fof(f180,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_4 ),
    inference(resolution,[],[f179,f76])).

fof(f234,plain,
    ( ~ spl5_31
    | spl5_26
    | spl5_32
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f202,f155,f232,f213,f226])).

fof(f226,plain,
    ( spl5_31
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f202,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)
    | ~ spl5_16 ),
    inference(resolution,[],[f178,f156])).

fof(f221,plain,
    ( ~ spl5_25
    | spl5_26
    | spl5_28
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f201,f148,f219,f213,f207])).

fof(f207,plain,
    ( spl5_25
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f201,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)
    | ~ spl5_14 ),
    inference(resolution,[],[f178,f149])).

fof(f199,plain,
    ( spl5_22
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f185,f155,f197])).

fof(f197,plain,
    ( spl5_22
  <=> k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f185,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2
    | ~ spl5_16 ),
    inference(resolution,[],[f92,f156])).

fof(f192,plain,
    ( spl5_20
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f184,f148,f190])).

fof(f190,plain,
    ( spl5_20
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f184,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1
    | ~ spl5_14 ),
    inference(resolution,[],[f92,f149])).

fof(f165,plain,(
    ~ spl5_19 ),
    inference(avatar_split_clause,[],[f71,f163])).

fof(f71,plain,(
    ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v4_pre_topc(sK2,sK0)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f59,f58,f57])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v4_pre_topc(X2,X0)
                & v4_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v4_pre_topc(X2,sK0)
              & v4_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v4_pre_topc(X2,X0)
            & v4_pre_topc(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v4_pre_topc(X2,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v4_pre_topc(sK2,X0)
        & v4_pre_topc(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',t36_tops_1)).

fof(f157,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f68,f155])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f150,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f67,f148])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f143,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f73,f141])).

fof(f141,plain,
    ( spl5_12
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f136,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f70,f134])).

fof(f70,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f129,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f69,f127])).

fof(f69,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f122,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f91,f120])).

fof(f120,plain,
    ( spl5_6
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f91,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f63])).

fof(f63,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK4) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',existence_l1_pre_topc)).

fof(f115,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f72,f113])).

fof(f72,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t36_tops_1.p',dt_o_0_0_xboole_0)).

fof(f108,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f66,f106])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f101,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f65,f99])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
