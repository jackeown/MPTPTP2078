%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t35_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:53 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 461 expanded)
%              Number of leaves         :   54 ( 172 expanded)
%              Depth                    :   12
%              Number of atoms          :  490 (1200 expanded)
%              Number of equality atoms :   20 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f432,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f110,f117,f124,f133,f140,f147,f154,f166,f175,f182,f191,f198,f216,f224,f232,f242,f250,f258,f275,f299,f308,f327,f335,f343,f361,f371,f381,f395,f410,f420,f430])).

fof(f430,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12
    | spl6_17
    | ~ spl6_18
    | ~ spl6_30
    | ~ spl6_38 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_30
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f428,f174])).

fof(f174,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl6_18
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f428,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_30
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f426,f274])).

fof(f274,plain,
    ( u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl6_38
  <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f426,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f102,f109,f165,f146,f231,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',d2_connsp_2)).

fof(f231,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl6_30
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f146,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f165,plain,
    ( ~ m2_connsp_2(u1_struct_0(sK0),sK0,sK1)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl6_17
  <=> ~ m2_connsp_2(u1_struct_0(sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f109,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f102,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f420,plain,
    ( ~ spl6_63
    | spl6_61 ),
    inference(avatar_split_clause,[],[f412,f408,f418])).

fof(f418,plain,
    ( spl6_63
  <=> ~ r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f408,plain,
    ( spl6_61
  <=> ~ m1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f412,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ spl6_61 ),
    inference(unit_resulting_resolution,[],[f409,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',t1_subset)).

fof(f409,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f408])).

fof(f410,plain,
    ( ~ spl6_61
    | spl6_59 ),
    inference(avatar_split_clause,[],[f396,f390,f408])).

fof(f390,plain,
    ( spl6_59
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f396,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl6_59 ),
    inference(unit_resulting_resolution,[],[f391,f281])).

fof(f281,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f263])).

fof(f263,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f234,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',t2_subset)).

fof(f234,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f84,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',antisymmetry_r2_hidden)).

fof(f391,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f390])).

fof(f395,plain,
    ( ~ spl6_57
    | spl6_58
    | spl6_45 ),
    inference(avatar_split_clause,[],[f328,f325,f393,f387])).

fof(f387,plain,
    ( spl6_57
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f393,plain,
    ( spl6_58
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f325,plain,
    ( spl6_45
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f328,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl6_45 ),
    inference(resolution,[],[f326,f84])).

fof(f326,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f325])).

fof(f381,plain,
    ( ~ spl6_55
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f313,f297,f379])).

fof(f379,plain,
    ( spl6_55
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f297,plain,
    ( spl6_40
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f313,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f298,f284])).

fof(f284,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f283,f94])).

fof(f94,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',t5_subset)).

fof(f283,plain,(
    ! [X2,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f281,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',t4_subset)).

fof(f298,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f297])).

fof(f371,plain,
    ( spl6_52
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f319,f145,f108,f101,f369])).

fof(f369,plain,
    ( spl6_52
  <=> m2_connsp_2(sK3(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f319,plain,
    ( m2_connsp_2(sK3(sK0,sK1),sK0,sK1)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f102,f109,f146,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m2_connsp_2(sK3(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m2_connsp_2(sK3(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_connsp_2(X2,X0,X1)
     => m2_connsp_2(sK3(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ? [X2] : m2_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',existence_m2_connsp_2)).

fof(f361,plain,
    ( ~ spl6_51
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f312,f248,f359])).

fof(f359,plain,
    ( spl6_51
  <=> ~ r2_hidden(u1_struct_0(sK5),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f248,plain,
    ( spl6_34
  <=> m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f312,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_struct_0(sK5))
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f249,f284])).

fof(f249,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f248])).

fof(f343,plain,
    ( ~ spl6_49
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f310,f214,f341])).

fof(f341,plain,
    ( spl6_49
  <=> ~ r2_hidden(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f214,plain,
    ( spl6_26
  <=> m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f310,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f215,f284])).

fof(f215,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f214])).

fof(f335,plain,
    ( ~ spl6_47
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f311,f230,f333])).

fof(f333,plain,
    ( spl6_47
  <=> ~ r2_hidden(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f311,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f231,f284])).

fof(f327,plain,
    ( ~ spl6_45
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f314,f145,f325])).

fof(f314,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f146,f284])).

fof(f308,plain,
    ( spl6_42
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f301,f297,f306])).

fof(f306,plain,
    ( spl6_42
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f301,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f298,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',t3_subset)).

fof(f299,plain,
    ( spl6_40
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f288,f145,f108,f297])).

fof(f288,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f109,f146,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',dt_k1_tops_1)).

fof(f275,plain,
    ( spl6_38
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f266,f189,f108,f101,f273])).

fof(f189,plain,
    ( spl6_22
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f266,plain,
    ( u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f264,f190])).

fof(f190,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f189])).

fof(f264,plain,
    ( k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f102,f109,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',t43_tops_1)).

fof(f258,plain,
    ( spl6_36
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f251,f248,f256])).

fof(f256,plain,
    ( spl6_36
  <=> r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f251,plain,
    ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5))
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f249,f89])).

fof(f250,plain,
    ( spl6_34
    | ~ spl6_10
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f207,f196,f138,f248])).

fof(f138,plain,
    ( spl6_10
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f196,plain,
    ( spl6_24
  <=> u1_struct_0(sK5) = k2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f207,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl6_10
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f201,f197])).

fof(f197,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f196])).

fof(f201,plain,
    ( m1_subset_1(k2_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f139,f76])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',dt_k2_struct_0)).

fof(f139,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f242,plain,
    ( spl6_32
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f235,f230,f240])).

fof(f240,plain,
    ( spl6_32
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f235,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f231,f89])).

fof(f232,plain,
    ( spl6_30
    | ~ spl6_8
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f208,f189,f131,f230])).

fof(f131,plain,
    ( spl6_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f208,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f200,f190])).

fof(f200,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f132,f76])).

fof(f132,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f224,plain,
    ( spl6_28
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f217,f214,f222])).

fof(f222,plain,
    ( spl6_28
  <=> r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f217,plain,
    ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f215,f89])).

fof(f216,plain,
    ( spl6_26
    | ~ spl6_4
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f209,f180,f115,f214])).

fof(f115,plain,
    ( spl6_4
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f180,plain,
    ( spl6_20
  <=> u1_struct_0(sK4) = k2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f209,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl6_4
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f199,f181])).

fof(f181,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f180])).

fof(f199,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f116,f76])).

fof(f116,plain,
    ( l1_struct_0(sK4)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f198,plain,
    ( spl6_24
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f157,f138,f196])).

fof(f157,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f139,f75])).

fof(f75,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',d3_struct_0)).

fof(f191,plain,
    ( spl6_22
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f156,f131,f189])).

fof(f156,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f132,f75])).

fof(f182,plain,
    ( spl6_20
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f155,f115,f180])).

fof(f155,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f116,f75])).

fof(f175,plain,
    ( spl6_18
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f168,f145,f173])).

fof(f168,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f146,f89])).

fof(f166,plain,
    ( ~ spl6_17
    | ~ spl6_8
    | spl6_15 ),
    inference(avatar_split_clause,[],[f159,f152,f131,f164])).

fof(f152,plain,
    ( spl6_15
  <=> ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f159,plain,
    ( ~ m2_connsp_2(u1_struct_0(sK0),sK0,sK1)
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f156,f153])).

fof(f153,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f152])).

fof(f154,plain,(
    ~ spl6_15 ),
    inference(avatar_split_clause,[],[f73,f152])).

fof(f73,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f58,f57])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ m2_connsp_2(k2_struct_0(X0),X0,sK1)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',t35_connsp_2)).

fof(f147,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f72,f145])).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f59])).

fof(f140,plain,
    ( spl6_10
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f126,f122,f138])).

fof(f122,plain,
    ( spl6_6
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f126,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f123,f77])).

fof(f77,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',dt_l1_pre_topc)).

fof(f123,plain,
    ( l1_pre_topc(sK5)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f133,plain,
    ( spl6_8
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f125,f108,f131])).

fof(f125,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f109,f77])).

fof(f124,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f96,f122])).

fof(f96,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f68])).

fof(f68,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK5) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',existence_l1_pre_topc)).

fof(f117,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f95,f115])).

fof(f95,plain,(
    l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    l1_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f66])).

fof(f66,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK4) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t35_connsp_2.p',existence_l1_struct_0)).

fof(f110,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f71,f108])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f103,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f70,f101])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
