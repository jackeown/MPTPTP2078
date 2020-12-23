%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : compts_1__t21_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:50 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 479 expanded)
%              Number of leaves         :   23 ( 210 expanded)
%              Depth                    :   16
%              Number of atoms          : 1175 (2291 expanded)
%              Number of equality atoms :   55 ( 108 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f899,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f102,f106,f110,f114,f118,f142,f146,f150,f155,f172,f176,f370,f374,f387,f391,f437,f441,f530,f898])).

fof(f898,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_11
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_52
    | ~ spl9_54
    | ~ spl9_62
    | ~ spl9_64
    | ~ spl9_72 ),
    inference(avatar_contradiction_clause,[],[f897])).

fof(f897,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_11
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_52
    | ~ spl9_54
    | ~ spl9_62
    | ~ spl9_64
    | ~ spl9_72 ),
    inference(subsumption_resolution,[],[f896,f436])).

fof(f436,plain,
    ( m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl9_62
  <=> m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f896,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_11
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_52
    | ~ spl9_54
    | ~ spl9_64
    | ~ spl9_72 ),
    inference(subsumption_resolution,[],[f895,f390])).

fof(f390,plain,
    ( r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_54 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl9_54
  <=> r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f895,plain,
    ( ~ r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_11
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_52
    | ~ spl9_64
    | ~ spl9_72 ),
    inference(subsumption_resolution,[],[f894,f373])).

fof(f373,plain,
    ( v3_pre_topc(sK6(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl9_46
  <=> v3_pre_topc(sK6(sK0,sK2(sK0),sK1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f894,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_11
    | ~ spl9_44
    | ~ spl9_52
    | ~ spl9_64
    | ~ spl9_72 ),
    inference(resolution,[],[f473,f529])).

fof(f529,plain,
    ( r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_72 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl9_72
  <=> r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),sK6(sK0,sK2(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f473,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),X0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(sK2(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_11
    | ~ spl9_44
    | ~ spl9_52
    | ~ spl9_64 ),
    inference(subsumption_resolution,[],[f472,f117])).

fof(f117,plain,
    ( ~ v9_pre_topc(sK0)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl9_11
  <=> ~ v9_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f472,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(sK2(sK0),X0)
        | ~ r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),X0)
        | v9_pre_topc(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_44
    | ~ spl9_52
    | ~ spl9_64 ),
    inference(subsumption_resolution,[],[f471,f386])).

fof(f386,plain,
    ( r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl9_52
  <=> r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f471,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
        | ~ r1_tarski(sK2(sK0),X0)
        | ~ r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),X0)
        | v9_pre_topc(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_44
    | ~ spl9_64 ),
    inference(subsumption_resolution,[],[f470,f369])).

fof(f369,plain,
    ( v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl9_44
  <=> v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f470,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
        | ~ r1_tarski(sK2(sK0),X0)
        | ~ r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),X0)
        | v9_pre_topc(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_64 ),
    inference(subsumption_resolution,[],[f469,f97])).

fof(f97,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f469,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
        | ~ r1_tarski(sK2(sK0),X0)
        | ~ r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),X0)
        | v9_pre_topc(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_64 ),
    inference(subsumption_resolution,[],[f468,f105])).

fof(f105,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl9_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f468,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
        | ~ r1_tarski(sK2(sK0),X0)
        | ~ r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),X0)
        | v9_pre_topc(sK0) )
    | ~ spl9_2
    | ~ spl9_64 ),
    inference(subsumption_resolution,[],[f461,f101])).

fof(f101,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl9_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f461,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
        | ~ r1_tarski(sK2(sK0),X0)
        | ~ r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),X0)
        | v9_pre_topc(sK0) )
    | ~ spl9_64 ),
    inference(resolution,[],[f440,f59])).

fof(f59,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ v3_pre_topc(X4,X0)
      | ~ r2_hidden(sK1(X0),X3)
      | ~ r1_tarski(sK2(X0),X4)
      | ~ r1_xboole_0(X3,X4)
      | v9_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v9_pre_topc(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( r1_xboole_0(X3,X4)
                        & r1_tarski(X2,X4)
                        & r2_hidden(X1,X3)
                        & v3_pre_topc(X4,X0)
                        & v3_pre_topc(X3,X0)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                | ~ v4_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v9_pre_topc(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( r1_xboole_0(X3,X4)
                        & r1_tarski(X2,X4)
                        & r2_hidden(X1,X3)
                        & v3_pre_topc(X4,X0)
                        & v3_pre_topc(X3,X0)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                | ~ v4_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_pre_topc(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ! [X4] :
                            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                           => ~ ( r1_xboole_0(X3,X4)
                                & r1_tarski(X2,X4)
                                & r2_hidden(X1,X3)
                                & v3_pre_topc(X4,X0)
                                & v3_pre_topc(X3,X0) ) ) )
                    & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                    & v4_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t21_compts_1.p',d5_compts_1)).

fof(f440,plain,
    ( m1_subset_1(sK5(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl9_64
  <=> m1_subset_1(sK5(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f530,plain,
    ( spl9_72
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f237,f174,f170,f153,f148,f140,f108,f104,f100,f528])).

fof(f108,plain,
    ( spl9_6
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f140,plain,
    ( spl9_13
  <=> k1_xboole_0 != sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f148,plain,
    ( spl9_16
  <=> m1_subset_1(sK1(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f153,plain,
    ( spl9_18
  <=> m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f170,plain,
    ( spl9_20
  <=> v2_compts_1(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f174,plain,
    ( spl9_22
  <=> r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f237,plain,
    ( r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f236,f101])).

fof(f236,plain,
    ( ~ v2_pre_topc(sK0)
    | r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f235,f149])).

fof(f149,plain,
    ( m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f235,plain,
    ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f234,f141])).

fof(f141,plain,
    ( k1_xboole_0 != sK2(sK0)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f234,plain,
    ( k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f233,f171])).

fof(f171,plain,
    ( v2_compts_1(sK2(sK0),sK0)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f170])).

fof(f233,plain,
    ( ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f232,f154])).

fof(f154,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f232,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f231,f109])).

fof(f109,plain,
    ( v8_pre_topc(sK0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f231,plain,
    ( ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f189,f105])).

fof(f189,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r1_xboole_0(sK5(sK0,sK2(sK0),sK1(sK0)),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_22 ),
    inference(resolution,[],[f175,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | r1_xboole_0(sK5(X0,X1,X2),sK6(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( r1_xboole_0(X3,X4)
                      & r1_tarski(X1,X4)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X4,X0)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_xboole_0 = X1
          | ~ v2_compts_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( r1_xboole_0(X3,X4)
                      & r1_tarski(X1,X4)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X4,X0)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_xboole_0 = X1
          | ~ v2_compts_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v8_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_compts_1(X1,X0)
             => ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ ( ! [X3] :
                            ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                           => ! [X4] :
                                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                               => ~ ( r1_xboole_0(X3,X4)
                                    & r1_tarski(X1,X4)
                                    & r2_hidden(X2,X3)
                                    & v3_pre_topc(X4,X0)
                                    & v3_pre_topc(X3,X0) ) ) )
                        & r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) ) )
                | k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t21_compts_1.p',t15_compts_1)).

fof(f175,plain,
    ( r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f174])).

fof(f441,plain,
    ( spl9_64
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f244,f174,f170,f153,f148,f140,f108,f104,f100,f439])).

fof(f244,plain,
    ( m1_subset_1(sK5(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f243,f101])).

fof(f243,plain,
    ( ~ v2_pre_topc(sK0)
    | m1_subset_1(sK5(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f242,f149])).

fof(f242,plain,
    ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK5(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f241,f141])).

fof(f241,plain,
    ( k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK5(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f240,f171])).

fof(f240,plain,
    ( ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK5(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f239,f154])).

fof(f239,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK5(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f238,f109])).

fof(f238,plain,
    ( ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK5(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f190,f105])).

fof(f190,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK5(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_22 ),
    inference(resolution,[],[f175,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f437,plain,
    ( spl9_62
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f202,f174,f170,f153,f148,f140,f108,f104,f100,f435])).

fof(f202,plain,
    ( m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f201,f101])).

fof(f201,plain,
    ( ~ v2_pre_topc(sK0)
    | m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f200,f149])).

fof(f200,plain,
    ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f199,f141])).

fof(f199,plain,
    ( k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f198,f171])).

fof(f198,plain,
    ( ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f197,f154])).

fof(f197,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f196,f109])).

fof(f196,plain,
    ( ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f184,f105])).

fof(f184,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_22 ),
    inference(resolution,[],[f175,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f391,plain,
    ( spl9_54
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f230,f174,f170,f153,f148,f140,f108,f104,f100,f389])).

fof(f230,plain,
    ( r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f229,f101])).

fof(f229,plain,
    ( ~ v2_pre_topc(sK0)
    | r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f228,f149])).

fof(f228,plain,
    ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f227,f141])).

fof(f227,plain,
    ( k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f226,f171])).

fof(f226,plain,
    ( ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f225,f154])).

fof(f225,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f224,f109])).

fof(f224,plain,
    ( ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f188,f105])).

fof(f188,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_22 ),
    inference(resolution,[],[f175,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | r1_tarski(X1,sK6(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f387,plain,
    ( spl9_52
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f223,f174,f170,f153,f148,f140,f108,f104,f100,f385])).

fof(f223,plain,
    ( r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f222,f101])).

fof(f222,plain,
    ( ~ v2_pre_topc(sK0)
    | r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f221,f149])).

fof(f221,plain,
    ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f220,f141])).

fof(f220,plain,
    ( k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f219,f171])).

fof(f219,plain,
    ( ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f218,f154])).

fof(f218,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f217,f109])).

fof(f217,plain,
    ( ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_4
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f187,f105])).

fof(f187,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl9_22 ),
    inference(resolution,[],[f175,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | r2_hidden(X2,sK5(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f374,plain,
    ( spl9_46
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f216,f174,f170,f153,f148,f140,f108,f104,f100,f372])).

fof(f216,plain,
    ( v3_pre_topc(sK6(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f215,f101])).

fof(f215,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK6(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f214,f149])).

fof(f214,plain,
    ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK6(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f213,f141])).

fof(f213,plain,
    ( k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK6(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f212,f171])).

fof(f212,plain,
    ( ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK6(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f211,f154])).

fof(f211,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK6(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f210,f109])).

fof(f210,plain,
    ( ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK6(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_4
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f186,f105])).

fof(f186,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK6(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_22 ),
    inference(resolution,[],[f175,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(sK6(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f370,plain,
    ( spl9_44
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f209,f174,f170,f153,f148,f140,f108,f104,f100,f368])).

fof(f209,plain,
    ( v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f208,f101])).

fof(f208,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f207,f149])).

fof(f207,plain,
    ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f206,f141])).

fof(f206,plain,
    ( k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f205,f171])).

fof(f205,plain,
    ( ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f204,f154])).

fof(f204,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f203,f109])).

fof(f203,plain,
    ( ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_4
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f185,f105])).

fof(f185,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl9_22 ),
    inference(resolution,[],[f175,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(sK5(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f176,plain,
    ( spl9_22
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_11 ),
    inference(avatar_split_clause,[],[f135,f116,f104,f100,f96,f174])).

fof(f135,plain,
    ( r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f134,f117])).

fof(f134,plain,
    ( r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | v9_pre_topc(sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f133,f97])).

fof(f133,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | v9_pre_topc(sK0)
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f122,f101])).

fof(f122,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | v9_pre_topc(sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f105,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
      | v9_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f172,plain,
    ( spl9_20
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f164,f153,f144,f112,f104,f170])).

fof(f112,plain,
    ( spl9_8
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f144,plain,
    ( spl9_14
  <=> v4_pre_topc(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f164,plain,
    ( v2_compts_1(sK2(sK0),sK0)
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f163,f145])).

fof(f145,plain,
    ( v4_pre_topc(sK2(sK0),sK0)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f163,plain,
    ( ~ v4_pre_topc(sK2(sK0),sK0)
    | v2_compts_1(sK2(sK0),sK0)
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f162,f113])).

fof(f113,plain,
    ( v1_compts_1(sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f162,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v4_pre_topc(sK2(sK0),sK0)
    | v2_compts_1(sK2(sK0),sK0)
    | ~ spl9_4
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f156,f105])).

fof(f156,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v4_pre_topc(sK2(sK0),sK0)
    | v2_compts_1(sK2(sK0),sK0)
    | ~ spl9_18 ),
    inference(resolution,[],[f154,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v4_pre_topc(X1,X0)
      | v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t21_compts_1.p',t17_compts_1)).

fof(f155,plain,
    ( spl9_18
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_11 ),
    inference(avatar_split_clause,[],[f126,f116,f104,f100,f96,f153])).

fof(f126,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f125,f117])).

fof(f125,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v9_pre_topc(sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f124,f97])).

fof(f124,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v9_pre_topc(sK0)
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f119,f101])).

fof(f119,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v9_pre_topc(sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f105,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v9_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f150,plain,
    ( spl9_16
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_11 ),
    inference(avatar_split_clause,[],[f138,f116,f104,f100,f96,f148])).

fof(f138,plain,
    ( m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f137,f117])).

fof(f137,plain,
    ( m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | v9_pre_topc(sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f136,f97])).

fof(f136,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | v9_pre_topc(sK0)
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f123,f101])).

fof(f123,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | v9_pre_topc(sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f105,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(sK1(X0),u1_struct_0(X0))
      | v9_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f146,plain,
    ( spl9_14
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_11 ),
    inference(avatar_split_clause,[],[f132,f116,f104,f100,f96,f144])).

fof(f132,plain,
    ( v4_pre_topc(sK2(sK0),sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f131,f117])).

fof(f131,plain,
    ( v4_pre_topc(sK2(sK0),sK0)
    | v9_pre_topc(sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f130,f97])).

fof(f130,plain,
    ( v2_struct_0(sK0)
    | v4_pre_topc(sK2(sK0),sK0)
    | v9_pre_topc(sK0)
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f121,f101])).

fof(f121,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v4_pre_topc(sK2(sK0),sK0)
    | v9_pre_topc(sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f105,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v4_pre_topc(sK2(X0),X0)
      | v9_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f142,plain,
    ( ~ spl9_13
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_11 ),
    inference(avatar_split_clause,[],[f129,f116,f104,f100,f96,f140])).

fof(f129,plain,
    ( k1_xboole_0 != sK2(sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f128,f117])).

fof(f128,plain,
    ( k1_xboole_0 != sK2(sK0)
    | v9_pre_topc(sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f127,f97])).

fof(f127,plain,
    ( v2_struct_0(sK0)
    | k1_xboole_0 != sK2(sK0)
    | v9_pre_topc(sK0)
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f120,f101])).

fof(f120,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k1_xboole_0 != sK2(sK0)
    | v9_pre_topc(sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f105,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 != sK2(X0)
      | v9_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f118,plain,(
    ~ spl9_11 ),
    inference(avatar_split_clause,[],[f58,f116])).

fof(f58,plain,(
    ~ v9_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ~ v9_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ~ v9_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ( v1_compts_1(X0)
            & v8_pre_topc(X0) )
         => v9_pre_topc(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ( v1_compts_1(X0)
          & v8_pre_topc(X0) )
       => v9_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t21_compts_1.p',t21_compts_1)).

fof(f114,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f57,f112])).

fof(f57,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f110,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f56,f108])).

fof(f56,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f106,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f55,f104])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f54,f100])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f53,f96])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
