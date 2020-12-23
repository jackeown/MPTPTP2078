%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t32_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:51 EDT 2019

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 342 expanded)
%              Number of leaves         :   49 ( 131 expanded)
%              Depth                    :   11
%              Number of atoms          :  658 (1122 expanded)
%              Number of equality atoms :   47 (  91 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1755,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f132,f139,f155,f162,f170,f177,f189,f214,f218,f283,f290,f312,f374,f378,f506,f507,f576,f637,f820,f1171,f1172,f1173,f1396,f1602,f1619,f1626,f1754])).

fof(f1754,plain,
    ( ~ spl10_34
    | ~ spl10_52
    | ~ spl10_224
    | spl10_261 ),
    inference(avatar_contradiction_clause,[],[f1753])).

fof(f1753,plain,
    ( $false
    | ~ spl10_34
    | ~ spl10_52
    | ~ spl10_224
    | ~ spl10_261 ),
    inference(subsumption_resolution,[],[f1747,f1581])).

fof(f1581,plain,
    ( ~ r2_hidden(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK1)
    | ~ spl10_261 ),
    inference(avatar_component_clause,[],[f1580])).

fof(f1580,plain,
    ( spl10_261
  <=> ~ r2_hidden(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_261])])).

fof(f1747,plain,
    ( r2_hidden(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK1)
    | ~ spl10_34
    | ~ spl10_52
    | ~ spl10_224 ),
    inference(resolution,[],[f1632,f1395])).

fof(f1395,plain,
    ( m1_subset_1(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK1)
    | ~ spl10_224 ),
    inference(avatar_component_clause,[],[f1394])).

fof(f1394,plain,
    ( spl10_224
  <=> m1_subset_1(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_224])])).

fof(f1632,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(X0,sK1) )
    | ~ spl10_34
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f1409,f276])).

fof(f276,plain,
    ( sP6(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl10_34
  <=> sP6(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f1409,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,sK1)
        | ~ sP6(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0)) )
    | ~ spl10_52 ),
    inference(resolution,[],[f1305,f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(sK7(X0,X1,X3),X1)
      | ~ sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_cantor_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> ? [X4] :
                      ( k8_setfam_1(X0,X4) = X3
                      & v1_finset_1(X4)
                      & r1_tarski(X4,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k2_cantor_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> ? [X4] :
                      ( k8_setfam_1(X0,X4) = X3
                      & v1_finset_1(X4)
                      & r1_tarski(X4,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t32_yellow19.p',d4_cantor_1)).

fof(f1305,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),X1)
        | r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl10_52 ),
    inference(resolution,[],[f1140,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t32_yellow19.p',t3_subset)).

fof(f1140,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | r2_hidden(X1,X0) )
    | ~ spl10_52 ),
    inference(resolution,[],[f1081,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/yellow19__t32_yellow19.p',t2_subset)).

fof(f1081,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(X0)) )
    | ~ spl10_52 ),
    inference(resolution,[],[f367,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t32_yellow19.p',t5_subset)).

fof(f367,plain,
    ( r2_hidden(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))))
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl10_52
  <=> r2_hidden(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f1626,plain,
    ( ~ spl10_40
    | spl10_49
    | ~ spl10_50
    | spl10_55
    | ~ spl10_266 ),
    inference(avatar_contradiction_clause,[],[f1625])).

fof(f1625,plain,
    ( $false
    | ~ spl10_40
    | ~ spl10_49
    | ~ spl10_50
    | ~ spl10_55
    | ~ spl10_266 ),
    inference(subsumption_resolution,[],[f1624,f370])).

fof(f370,plain,
    ( ~ v4_pre_topc(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl10_55 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl10_55
  <=> ~ v4_pre_topc(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f1624,plain,
    ( v4_pre_topc(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl10_40
    | ~ spl10_49
    | ~ spl10_50
    | ~ spl10_266 ),
    inference(forward_demodulation,[],[f1623,f311])).

fof(f311,plain,
    ( k8_setfam_1(u1_struct_0(sK0),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))) = sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl10_40
  <=> k8_setfam_1(u1_struct_0(sK0),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))) = sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f1623,plain,
    ( v4_pre_topc(k8_setfam_1(u1_struct_0(sK0),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ spl10_49
    | ~ spl10_50
    | ~ spl10_266 ),
    inference(subsumption_resolution,[],[f1622,f358])).

fof(f358,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl10_50
  <=> m1_subset_1(sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f1622,plain,
    ( v4_pre_topc(k8_setfam_1(u1_struct_0(sK0),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ m1_subset_1(sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_49
    | ~ spl10_266 ),
    inference(subsumption_resolution,[],[f1620,f352])).

fof(f352,plain,
    ( k1_xboole_0 != sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl10_49
  <=> k1_xboole_0 != sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f1620,plain,
    ( v4_pre_topc(k8_setfam_1(u1_struct_0(sK0),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | k1_xboole_0 = sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_266 ),
    inference(superposition,[],[f1618,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t32_yellow19.p',d10_setfam_1)).

fof(f1618,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ spl10_266 ),
    inference(avatar_component_clause,[],[f1617])).

fof(f1617,plain,
    ( spl10_266
  <=> v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_266])])).

fof(f1619,plain,
    ( spl10_266
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_50
    | ~ spl10_92 ),
    inference(avatar_split_clause,[],[f1605,f536,f357,f130,f123,f1617])).

fof(f123,plain,
    ( spl10_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f130,plain,
    ( spl10_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f536,plain,
    ( spl10_92
  <=> v4_pre_topc(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f1605,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_50
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1604,f358])).

fof(f1604,plain,
    ( ~ m1_subset_1(sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_92 ),
    inference(resolution,[],[f537,f147])).

fof(f147,plain,
    ( ! [X1] :
        ( ~ v4_pre_topc(sK3(sK0,X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X1),sK0) )
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f141,f124])).

fof(f124,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f141,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v4_pre_topc(sK3(sK0,X1),sK0)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X1),sK0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f131,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v4_pre_topc(sK3(X0,X1),X0)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t32_yellow19.p',t44_pre_topc)).

fof(f131,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f537,plain,
    ( v4_pre_topc(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ spl10_92 ),
    inference(avatar_component_clause,[],[f536])).

fof(f1602,plain,
    ( ~ spl10_4
    | ~ spl10_6
    | ~ spl10_10
    | spl10_93
    | ~ spl10_260 ),
    inference(avatar_contradiction_clause,[],[f1601])).

fof(f1601,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_93
    | ~ spl10_260 ),
    inference(subsumption_resolution,[],[f1600,f138])).

fof(f138,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl10_6
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f1600,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_93
    | ~ spl10_260 ),
    inference(subsumption_resolution,[],[f1599,f534])).

fof(f534,plain,
    ( ~ v4_pre_topc(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ spl10_93 ),
    inference(avatar_component_clause,[],[f533])).

fof(f533,plain,
    ( spl10_93
  <=> ~ v4_pre_topc(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).

fof(f1599,plain,
    ( v4_pre_topc(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ v2_tops_2(sK1,sK0)
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_260 ),
    inference(subsumption_resolution,[],[f1593,f161])).

fof(f161,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl10_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f1593,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v4_pre_topc(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ v2_tops_2(sK1,sK0)
    | ~ spl10_4
    | ~ spl10_260 ),
    inference(resolution,[],[f1584,f148])).

fof(f148,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v4_pre_topc(X3,sK0)
        | ~ v2_tops_2(X2,sK0) )
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f142,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t32_yellow19.p',t4_subset)).

fof(f142,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X3,X2)
        | v4_pre_topc(X3,sK0)
        | ~ v2_tops_2(X2,sK0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f131,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v4_pre_topc(X2,X0)
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t32_yellow19.p',d2_tops_2)).

fof(f1584,plain,
    ( r2_hidden(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK1)
    | ~ spl10_260 ),
    inference(avatar_component_clause,[],[f1583])).

fof(f1583,plain,
    ( spl10_260
  <=> r2_hidden(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_260])])).

fof(f1396,plain,
    ( spl10_224
    | ~ spl10_34
    | ~ spl10_52 ),
    inference(avatar_split_clause,[],[f1322,f366,f275,f1394])).

fof(f1322,plain,
    ( m1_subset_1(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK1)
    | ~ spl10_34
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f1320,f276])).

fof(f1320,plain,
    ( m1_subset_1(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK1)
    | ~ sP6(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | ~ spl10_52 ),
    inference(resolution,[],[f1141,f92])).

fof(f1141,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),X0)
        | m1_subset_1(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),X0) )
    | ~ spl10_52 ),
    inference(resolution,[],[f1082,f100])).

fof(f1082,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(X1))
        | m1_subset_1(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),X1) )
    | ~ spl10_52 ),
    inference(resolution,[],[f367,f104])).

fof(f1173,plain,
    ( k1_xboole_0 != sK7(u1_struct_0(sK0),sK1,k8_setfam_1(u1_struct_0(sK0),k1_xboole_0))
    | ~ m1_subset_1(sK7(u1_struct_0(sK0),sK1,k8_setfam_1(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(theory_axiom,[])).

fof(f1172,plain,
    ( u1_struct_0(sK0) != k8_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | v4_pre_topc(k8_setfam_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ v4_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(theory_axiom,[])).

fof(f1171,plain,
    ( spl10_194
    | ~ spl10_106 ),
    inference(avatar_split_clause,[],[f1111,f651,f1169])).

fof(f1169,plain,
    ( spl10_194
  <=> u1_struct_0(sK0) = k8_setfam_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_194])])).

fof(f651,plain,
    ( spl10_106
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_106])])).

fof(f1111,plain,
    ( u1_struct_0(sK0) = k8_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl10_106 ),
    inference(resolution,[],[f652,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f652,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_106 ),
    inference(avatar_component_clause,[],[f651])).

fof(f820,plain,
    ( spl10_140
    | ~ spl10_50
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f587,f389,f357,f818])).

fof(f818,plain,
    ( spl10_140
  <=> m1_subset_1(sK7(u1_struct_0(sK0),sK1,k8_setfam_1(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_140])])).

fof(f389,plain,
    ( spl10_58
  <=> k8_setfam_1(u1_struct_0(sK0),k1_xboole_0) = sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f587,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),sK1,k8_setfam_1(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_50
    | ~ spl10_58 ),
    inference(superposition,[],[f358,f390])).

fof(f390,plain,
    ( k8_setfam_1(u1_struct_0(sK0),k1_xboole_0) = sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f389])).

fof(f637,plain,
    ( ~ spl10_103
    | spl10_55
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f588,f389,f369,f635])).

fof(f635,plain,
    ( spl10_103
  <=> ~ v4_pre_topc(k8_setfam_1(u1_struct_0(sK0),k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_103])])).

fof(f588,plain,
    ( ~ v4_pre_topc(k8_setfam_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ spl10_55
    | ~ spl10_58 ),
    inference(superposition,[],[f370,f390])).

fof(f576,plain,
    ( ~ spl10_4
    | spl10_13
    | ~ spl10_20
    | ~ spl10_54 ),
    inference(avatar_contradiction_clause,[],[f575])).

fof(f575,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_13
    | ~ spl10_20
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f574,f169])).

fof(f169,plain,
    ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl10_13
  <=> ~ v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f574,plain,
    ( v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl10_4
    | ~ spl10_20
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f573,f204])).

fof(f204,plain,
    ( m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl10_20
  <=> m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f573,plain,
    ( ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl10_4
    | ~ spl10_54 ),
    inference(resolution,[],[f373,f144])).

fof(f144,plain,
    ( ! [X5] :
        ( ~ v4_pre_topc(sK2(sK0,X5),sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X5,sK0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f131,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v4_pre_topc(sK2(X0,X1),X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f373,plain,
    ( v4_pre_topc(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl10_54
  <=> v4_pre_topc(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f507,plain,
    ( k1_xboole_0 != sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))
    | k8_setfam_1(u1_struct_0(sK0),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))) != sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))
    | k8_setfam_1(u1_struct_0(sK0),k1_xboole_0) = sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)) ),
    introduced(theory_axiom,[])).

fof(f506,plain,
    ( k8_setfam_1(u1_struct_0(sK0),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))) != sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))
    | k1_xboole_0 != sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))
    | k1_xboole_0 = sK7(u1_struct_0(sK0),sK1,k8_setfam_1(u1_struct_0(sK0),k1_xboole_0)) ),
    introduced(theory_axiom,[])).

fof(f378,plain,
    ( ~ spl10_34
    | spl10_51 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | ~ spl10_34
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f375,f276])).

fof(f375,plain,
    ( ~ sP6(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | ~ spl10_51 ),
    inference(resolution,[],[f361,f91])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f361,plain,
    ( ~ m1_subset_1(sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_51 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl10_51
  <=> ~ m1_subset_1(sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f374,plain,
    ( spl10_48
    | ~ spl10_51
    | spl10_52
    | spl10_54
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f322,f310,f130,f123,f372,f366,f360,f354])).

fof(f354,plain,
    ( spl10_48
  <=> k1_xboole_0 = sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f322,plain,
    ( v4_pre_topc(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK0)
    | r2_hidden(sK3(sK0,sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))))
    | ~ m1_subset_1(sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_40 ),
    inference(superposition,[],[f201,f311])).

fof(f201,plain,
    ( ! [X0] :
        ( v4_pre_topc(k8_setfam_1(u1_struct_0(sK0),X0),sK0)
        | r2_hidden(sK3(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X0 )
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(duplicate_literal_removal,[],[f198])).

fof(f198,plain,
    ( ! [X0] :
        ( v4_pre_topc(k8_setfam_1(u1_struct_0(sK0),X0),sK0)
        | r2_hidden(sK3(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(superposition,[],[f146,f89])).

fof(f146,plain,
    ( ! [X0] :
        ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X0),sK0)
        | r2_hidden(sK3(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f140,f124])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r2_hidden(sK3(sK0,X0),X0)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X0),sK0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f131,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK3(X0,X1),X1)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f312,plain,
    ( spl10_40
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f293,f275,f310])).

fof(f293,plain,
    ( k8_setfam_1(u1_struct_0(sK0),sK7(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))) = sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))
    | ~ spl10_34 ),
    inference(resolution,[],[f276,f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | k8_setfam_1(X0,sK7(X0,X1,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f290,plain,
    ( ~ spl10_4
    | spl10_13
    | ~ spl10_20
    | spl10_37 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_13
    | ~ spl10_20
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f288,f169])).

fof(f288,plain,
    ( v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl10_4
    | ~ spl10_20
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f287,f131])).

fof(f287,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl10_20
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f284,f204])).

fof(f284,plain,
    ( ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl10_37 ),
    inference(resolution,[],[f282,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f282,plain,
    ( ~ m1_subset_1(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl10_37
  <=> ~ m1_subset_1(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f283,plain,
    ( spl10_34
    | ~ spl10_37
    | ~ spl10_10
    | ~ spl10_20
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f227,f212,f203,f160,f281,f275])).

fof(f212,plain,
    ( spl10_22
  <=> r2_hidden(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k2_cantor_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f227,plain,
    ( ~ m1_subset_1(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP6(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | ~ spl10_10
    | ~ spl10_20
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f226,f161])).

fof(f226,plain,
    ( ~ m1_subset_1(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP6(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_20
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f219,f204])).

fof(f219,plain,
    ( ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP6(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_22 ),
    inference(resolution,[],[f213,f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_cantor_1(X0,X1))
      | ~ m1_subset_1(k2_cantor_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | sP6(X3,X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_cantor_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f213,plain,
    ( r2_hidden(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k2_cantor_1(u1_struct_0(sK0),sK1))
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f212])).

fof(f218,plain,
    ( ~ spl10_10
    | spl10_21 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f215,f161])).

fof(f215,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_21 ),
    inference(resolution,[],[f207,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_cantor_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_cantor_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k2_cantor_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t32_yellow19.p',dt_k2_cantor_1)).

fof(f207,plain,
    ( ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl10_21
  <=> ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f214,plain,
    ( ~ spl10_21
    | spl10_22
    | ~ spl10_4
    | spl10_13 ),
    inference(avatar_split_clause,[],[f190,f168,f130,f212,f206])).

fof(f190,plain,
    ( r2_hidden(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k2_cantor_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_4
    | ~ spl10_13 ),
    inference(resolution,[],[f143,f169])).

fof(f143,plain,
    ( ! [X4] :
        ( v2_tops_2(X4,sK0)
        | r2_hidden(sK2(sK0,X4),X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl10_4 ),
    inference(resolution,[],[f131,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK2(X0,X1),X1)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f189,plain,
    ( spl10_16
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f181,f175,f130,f123,f187])).

fof(f187,plain,
    ( spl10_16
  <=> v4_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f175,plain,
    ( spl10_14
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f181,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f180,f124])).

fof(f180,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_4
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f178,f131])).

fof(f178,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_14 ),
    inference(superposition,[],[f76,f176])).

fof(f176,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f175])).

fof(f76,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t32_yellow19.p',fc4_pre_topc)).

fof(f177,plain,
    ( spl10_14
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f163,f153,f175])).

fof(f153,plain,
    ( spl10_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f163,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl10_8 ),
    inference(resolution,[],[f154,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t32_yellow19.p',d3_struct_0)).

fof(f154,plain,
    ( l1_struct_0(sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f153])).

fof(f170,plain,(
    ~ spl10_13 ),
    inference(avatar_split_clause,[],[f63,f168])).

fof(f63,plain,(
    ~ v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
             => v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
           => v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t32_yellow19.p',t32_yellow19)).

fof(f162,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f61,f160])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f155,plain,
    ( spl10_8
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f145,f130,f153])).

fof(f145,plain,
    ( l1_struct_0(sK0)
    | ~ spl10_4 ),
    inference(resolution,[],[f131,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t32_yellow19.p',dt_l1_pre_topc)).

fof(f139,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f62,f137])).

fof(f62,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f132,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f66,f130])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f125,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f65,f123])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
