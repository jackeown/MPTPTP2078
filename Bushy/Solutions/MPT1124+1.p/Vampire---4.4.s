%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t55_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:44 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 383 expanded)
%              Number of leaves         :   46 ( 148 expanded)
%              Depth                    :   11
%              Number of atoms          :  468 ( 992 expanded)
%              Number of equality atoms :   34 (  88 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1635,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f107,f114,f121,f128,f135,f142,f157,f240,f257,f318,f340,f409,f439,f486,f553,f611,f680,f741,f748,f821,f840,f853,f1161,f1290,f1408,f1566,f1634])).

fof(f1634,plain,
    ( ~ spl9_8
    | spl9_11
    | spl9_27
    | ~ spl9_46 ),
    inference(avatar_contradiction_clause,[],[f1633])).

fof(f1633,plain,
    ( $false
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_27
    | ~ spl9_46 ),
    inference(subsumption_resolution,[],[f1631,f134])).

fof(f134,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl9_11
  <=> ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f1631,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_8
    | ~ spl9_27
    | ~ spl9_46 ),
    inference(resolution,[],[f1503,f127])).

fof(f127,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl9_8
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f1503,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_27
    | ~ spl9_46 ),
    inference(subsumption_resolution,[],[f1502,f408])).

fof(f408,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl9_27
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f1502,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl9_46 ),
    inference(resolution,[],[f1216,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',t2_subset)).

fof(f1216,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,u1_struct_0(sK1))
        | m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl9_46 ),
    inference(resolution,[],[f1160,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f65,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',t3_subset)).

fof(f65,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',t4_subset)).

fof(f1160,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f1159])).

fof(f1159,plain,
    ( spl9_46
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f1566,plain,
    ( ~ spl9_55
    | spl9_56
    | spl9_53 ),
    inference(avatar_split_clause,[],[f1438,f1406,f1564,f1558])).

fof(f1558,plain,
    ( spl9_55
  <=> ~ m1_subset_1(u1_struct_0(sK8),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f1564,plain,
    ( spl9_56
  <=> v1_xboole_0(u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f1406,plain,
    ( spl9_53
  <=> ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).

fof(f1438,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | ~ m1_subset_1(u1_struct_0(sK8),u1_pre_topc(sK0))
    | ~ spl9_53 ),
    inference(resolution,[],[f1407,f72])).

fof(f1407,plain,
    ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK0))
    | ~ spl9_53 ),
    inference(avatar_component_clause,[],[f1406])).

fof(f1408,plain,
    ( ~ spl9_53
    | ~ spl9_4
    | spl9_51 ),
    inference(avatar_split_clause,[],[f1358,f1285,f112,f1406])).

fof(f112,plain,
    ( spl9_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f1285,plain,
    ( spl9_51
  <=> ~ r1_tarski(u1_struct_0(sK8),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f1358,plain,
    ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK0))
    | ~ spl9_4
    | ~ spl9_51 ),
    inference(subsumption_resolution,[],[f1357,f113])).

fof(f113,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f1357,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK0))
    | ~ spl9_51 ),
    inference(resolution,[],[f1286,f327])).

fof(f327,plain,(
    ! [X15,X16] :
      ( r1_tarski(X15,u1_struct_0(X16))
      | ~ l1_pre_topc(X16)
      | ~ r2_hidden(X15,u1_pre_topc(X16)) ) ),
    inference(resolution,[],[f166,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f166,plain,(
    ! [X6,X5] :
      ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ r2_hidden(X5,u1_pre_topc(X6))
      | ~ l1_pre_topc(X6) ) ),
    inference(resolution,[],[f65,f86])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',dt_u1_pre_topc)).

fof(f1286,plain,
    ( ~ r1_tarski(u1_struct_0(sK8),u1_struct_0(sK0))
    | ~ spl9_51 ),
    inference(avatar_component_clause,[],[f1285])).

fof(f1290,plain,
    ( ~ spl9_49
    | spl9_50
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1117,f739,f238,f140,f112,f1288,f1282])).

fof(f1282,plain,
    ( spl9_49
  <=> ~ m1_pre_topc(sK8,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f1288,plain,
    ( spl9_50
  <=> r1_tarski(u1_struct_0(sK8),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f140,plain,
    ( spl9_12
  <=> l1_pre_topc(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f238,plain,
    ( spl9_16
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f739,plain,
    ( spl9_36
  <=> u1_struct_0(sK8) = k2_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f1117,plain,
    ( r1_tarski(u1_struct_0(sK8),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK8,sK0)
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_36 ),
    inference(subsumption_resolution,[],[f1114,f141])).

fof(f141,plain,
    ( l1_pre_topc(sK8)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f1114,plain,
    ( r1_tarski(u1_struct_0(sK8),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK8)
    | ~ m1_pre_topc(sK8,sK0)
    | ~ spl9_4
    | ~ spl9_16
    | ~ spl9_36 ),
    inference(superposition,[],[f273,f740])).

fof(f740,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8)
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f739])).

fof(f273,plain,
    ( ! [X2] :
        ( r1_tarski(k2_struct_0(X2),u1_struct_0(sK0))
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(X2,sK0) )
    | ~ spl9_4
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f265,f113])).

fof(f265,plain,
    ( ! [X2] :
        ( r1_tarski(k2_struct_0(X2),u1_struct_0(sK0))
        | ~ l1_pre_topc(X2)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK0) )
    | ~ spl9_16 ),
    inference(superposition,[],[f85,f239])).

fof(f239,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f238])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',d9_pre_topc)).

fof(f1161,plain,
    ( spl9_46
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f1116,f255,f238,f155,f119,f112,f1159])).

fof(f119,plain,
    ( spl9_6
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f155,plain,
    ( spl9_14
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f255,plain,
    ( spl9_18
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f1116,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f1115,f120])).

fof(f120,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f1115,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f1111,f156])).

fof(f156,plain,
    ( l1_pre_topc(sK1)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f155])).

fof(f1111,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl9_4
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(superposition,[],[f273,f256])).

fof(f256,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f255])).

fof(f853,plain,
    ( spl9_44
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f823,f155,f851])).

fof(f851,plain,
    ( spl9_44
  <=> u1_struct_0(sK7(sK1)) = k2_struct_0(sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f823,plain,
    ( u1_struct_0(sK7(sK1)) = k2_struct_0(sK7(sK1))
    | ~ spl9_14 ),
    inference(resolution,[],[f198,f156])).

fof(f198,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(sK7(X0)) = k2_struct_0(sK7(X0)) ) ),
    inference(resolution,[],[f145,f148])).

fof(f148,plain,(
    ! [X0] :
      ( l1_pre_topc(sK7(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_pre_topc(sK7(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f89,f88])).

fof(f88,plain,(
    ! [X0] :
      ( m1_pre_topc(sK7(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',existence_m1_pre_topc)).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',dt_m1_pre_topc)).

fof(f145,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f87,f91])).

fof(f91,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',dt_l1_pre_topc)).

fof(f87,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',d3_struct_0)).

fof(f840,plain,
    ( spl9_42
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f822,f112,f838])).

fof(f838,plain,
    ( spl9_42
  <=> u1_struct_0(sK7(sK0)) = k2_struct_0(sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f822,plain,
    ( u1_struct_0(sK7(sK0)) = k2_struct_0(sK7(sK0))
    | ~ spl9_4 ),
    inference(resolution,[],[f198,f113])).

fof(f821,plain,
    ( spl9_40
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f697,f155,f819])).

fof(f819,plain,
    ( spl9_40
  <=> k3_xboole_0(u1_pre_topc(sK1),u1_pre_topc(sK1)) = u1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f697,plain,
    ( k3_xboole_0(u1_pre_topc(sK1),u1_pre_topc(sK1)) = u1_pre_topc(sK1)
    | ~ spl9_14 ),
    inference(superposition,[],[f383,f171])).

fof(f171,plain,(
    ! [X8,X7] : k9_subset_1(X7,X8,X8) = X8 ),
    inference(resolution,[],[f69,f74])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',existence_m1_subset_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',idempotence_k9_subset_1)).

fof(f383,plain,
    ( ! [X1] : k3_xboole_0(X1,u1_pre_topc(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X1,u1_pre_topc(sK1))
    | ~ spl9_14 ),
    inference(resolution,[],[f178,f156])).

fof(f178,plain,(
    ! [X10,X9] :
      ( ~ l1_pre_topc(X10)
      | k3_xboole_0(X9,u1_pre_topc(X10)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(X10)),X9,u1_pre_topc(X10)) ) ),
    inference(resolution,[],[f67,f86])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',redefinition_k9_subset_1)).

fof(f748,plain,
    ( spl9_38
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f689,f112,f746])).

fof(f746,plain,
    ( spl9_38
  <=> k3_xboole_0(u1_pre_topc(sK0),u1_pre_topc(sK0)) = u1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f689,plain,
    ( k3_xboole_0(u1_pre_topc(sK0),u1_pre_topc(sK0)) = u1_pre_topc(sK0)
    | ~ spl9_4 ),
    inference(superposition,[],[f382,f171])).

fof(f382,plain,
    ( ! [X0] : k3_xboole_0(X0,u1_pre_topc(sK0)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,u1_pre_topc(sK0))
    | ~ spl9_4 ),
    inference(resolution,[],[f178,f113])).

fof(f741,plain,
    ( spl9_36
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f199,f140,f739])).

fof(f199,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8)
    | ~ spl9_12 ),
    inference(resolution,[],[f145,f141])).

fof(f680,plain,
    ( ~ spl9_25
    | spl9_34
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f282,f255,f678,f401])).

fof(f401,plain,
    ( spl9_25
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f678,plain,
    ( spl9_34
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f282,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_struct_0(sK1)
    | ~ spl9_18 ),
    inference(superposition,[],[f75,f256])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',dt_k2_struct_0)).

fof(f611,plain,
    ( ~ spl9_21
    | spl9_32
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f263,f238,f609,f310])).

fof(f310,plain,
    ( spl9_21
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f609,plain,
    ( spl9_32
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f263,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl9_16 ),
    inference(superposition,[],[f75,f239])).

fof(f553,plain,
    ( ~ spl9_25
    | spl9_30
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f288,f255,f551,f401])).

fof(f551,plain,
    ( spl9_30
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f288,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ spl9_18 ),
    inference(superposition,[],[f158,f256])).

fof(f158,plain,(
    ! [X0] :
      ( r1_tarski(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f75,f71])).

fof(f486,plain,
    ( ~ spl9_21
    | spl9_28
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f269,f238,f484,f310])).

fof(f484,plain,
    ( spl9_28
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f269,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl9_16 ),
    inference(superposition,[],[f158,f239])).

fof(f439,plain,
    ( ~ spl9_14
    | spl9_25 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | ~ spl9_14
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f437,f156])).

fof(f437,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl9_25 ),
    inference(resolution,[],[f402,f91])).

fof(f402,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f401])).

fof(f409,plain,
    ( ~ spl9_25
    | ~ spl9_27
    | spl9_1
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f295,f255,f98,f407,f401])).

fof(f98,plain,
    ( spl9_1
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f295,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ spl9_1
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f286,f99])).

fof(f99,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f286,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_18 ),
    inference(superposition,[],[f92,f256])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',fc5_struct_0)).

fof(f340,plain,
    ( ~ spl9_4
    | spl9_21 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f338,f113])).

fof(f338,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl9_21 ),
    inference(resolution,[],[f311,f91])).

fof(f311,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f310])).

fof(f318,plain,
    ( ~ spl9_21
    | ~ spl9_23
    | spl9_3
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f275,f238,f105,f316,f310])).

fof(f316,plain,
    ( spl9_23
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f105,plain,
    ( spl9_3
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f275,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl9_3
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f267,f106])).

fof(f106,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f267,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_16 ),
    inference(superposition,[],[f92,f239])).

fof(f257,plain,
    ( spl9_18
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f197,f155,f255])).

fof(f197,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl9_14 ),
    inference(resolution,[],[f145,f156])).

fof(f240,plain,
    ( spl9_16
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f196,f112,f238])).

fof(f196,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f145,f113])).

fof(f157,plain,
    ( spl9_14
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f149,f119,f112,f155])).

fof(f149,plain,
    ( l1_pre_topc(sK1)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f146,f113])).

fof(f146,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl9_6 ),
    inference(resolution,[],[f89,f120])).

fof(f142,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f90,f140])).

fof(f90,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',existence_l1_pre_topc)).

fof(f135,plain,(
    ~ spl9_11 ),
    inference(avatar_split_clause,[],[f59,f133])).

fof(f59,plain,(
    ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(X0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(X0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',t55_pre_topc)).

fof(f128,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f58,f126])).

fof(f58,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f121,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f61,f119])).

fof(f61,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f63,f112])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,(
    ~ spl9_3 ),
    inference(avatar_split_clause,[],[f62,f105])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f100,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f60,f98])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
