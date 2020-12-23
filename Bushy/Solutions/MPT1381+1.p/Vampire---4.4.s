%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t6_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:54 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 317 expanded)
%              Number of leaves         :   44 ( 142 expanded)
%              Depth                    :    9
%              Number of atoms          :  455 (1081 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f345,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f103,f110,f117,f124,f131,f138,f145,f170,f185,f206,f217,f225,f235,f242,f260,f272,f286,f299,f318,f339,f344])).

fof(f344,plain,
    ( spl6_9
    | ~ spl6_26
    | ~ spl6_40
    | spl6_43 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_26
    | ~ spl6_40
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f341,f323])).

fof(f323,plain,
    ( m1_subset_1(sK2,sK1)
    | ~ spl6_26
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f224,f317,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',t4_subset)).

fof(f317,plain,
    ( r2_hidden(sK2,k1_tops_1(sK0,sK1))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl6_40
  <=> r2_hidden(sK2,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f224,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl6_26
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f341,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | ~ spl6_9
    | ~ spl6_43 ),
    inference(unit_resulting_resolution,[],[f123,f338,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',t2_subset)).

fof(f338,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl6_43
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f123,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_9
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f339,plain,
    ( ~ spl6_43
    | ~ spl6_26
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f325,f316,f223,f337])).

fof(f325,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_26
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f224,f317,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',t5_subset)).

fof(f318,plain,
    ( spl6_40
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f306,f143,f136,f129,f108,f101,f94,f316])).

fof(f94,plain,
    ( spl6_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f101,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f108,plain,
    ( spl6_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f129,plain,
    ( spl6_10
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f136,plain,
    ( spl6_12
  <=> m1_connsp_2(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f143,plain,
    ( spl6_14
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f306,plain,
    ( r2_hidden(sK2,k1_tops_1(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f95,f102,f109,f137,f130,f144,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',d1_connsp_2)).

fof(f144,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f143])).

fof(f130,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f137,plain,
    ( m1_connsp_2(sK1,sK0,sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f109,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f102,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f95,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f299,plain,
    ( spl6_38
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f289,f233,f129,f108,f101,f94,f297])).

fof(f297,plain,
    ( spl6_38
  <=> m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f233,plain,
    ( spl6_28
  <=> m1_connsp_2(sK4(sK0,sK2),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f289,plain,
    ( m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(unit_resulting_resolution,[],[f95,f102,f109,f234,f130,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',dt_m1_connsp_2)).

fof(f234,plain,
    ( m1_connsp_2(sK4(sK0,sK2),sK0,sK2)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f233])).

fof(f286,plain,
    ( spl6_36
    | ~ spl6_4
    | ~ spl6_14
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f277,f270,f143,f108,f284])).

fof(f284,plain,
    ( spl6_36
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f270,plain,
    ( spl6_34
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f277,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_14
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f275,f261])).

fof(f261,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f109,f144,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',projectivity_k1_tops_1)).

fof(f275,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f109,f271,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',t44_tops_1)).

fof(f271,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f270])).

fof(f272,plain,
    ( spl6_34
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f209,f143,f108,f270])).

fof(f209,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f109,f144,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',dt_k1_tops_1)).

fof(f260,plain,
    ( ~ spl6_33
    | spl6_17 ),
    inference(avatar_split_clause,[],[f174,f159,f258])).

fof(f258,plain,
    ( spl6_33
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f159,plain,
    ( spl6_17
  <=> u1_struct_0(sK0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f174,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(u1_struct_0(sK0)))
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f160,f157])).

fof(f157,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,sK3(X7))
      | k1_xboole_0 = X7 ) ),
    inference(resolution,[],[f152,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',antisymmetry_r2_hidden)).

fof(f152,plain,(
    ! [X2] :
      ( r2_hidden(sK3(X2),X2)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f148,f76])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',existence_m1_subset_1)).

fof(f148,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,X7)
      | r2_hidden(X6,X7)
      | k1_xboole_0 = X7 ) ),
    inference(resolution,[],[f79,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',t6_boole)).

fof(f160,plain,
    ( u1_struct_0(sK0) != k1_xboole_0
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f159])).

fof(f242,plain,
    ( spl6_30
    | spl6_17 ),
    inference(avatar_split_clause,[],[f177,f159,f240])).

fof(f240,plain,
    ( spl6_30
  <=> r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f177,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f76,f160,f148])).

fof(f235,plain,
    ( spl6_28
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f227,f129,f108,f101,f94,f233])).

fof(f227,plain,
    ( m1_connsp_2(sK4(sK0,sK2),sK0,sK2)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f95,f102,f109,f130,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK4(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK4(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK4(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',existence_m1_connsp_2)).

fof(f225,plain,
    ( spl6_26
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f218,f215,f223])).

fof(f215,plain,
    ( spl6_24
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f218,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f216,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',t3_subset)).

fof(f216,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f215])).

fof(f217,plain,
    ( spl6_24
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f173,f143,f108,f215])).

fof(f173,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f109,f144,f73])).

fof(f206,plain,
    ( ~ spl6_23
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f190,f168,f204])).

fof(f204,plain,
    ( spl6_23
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f168,plain,
    ( spl6_18
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f190,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2)
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f169,f77])).

fof(f169,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f185,plain,
    ( ~ spl6_21
    | spl6_17 ),
    inference(avatar_split_clause,[],[f178,f159,f183])).

fof(f183,plain,
    ( spl6_21
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f178,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f160,f72])).

fof(f170,plain,
    ( spl6_16
    | spl6_18
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f151,f129,f168,f162])).

fof(f162,plain,
    ( spl6_16
  <=> u1_struct_0(sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f151,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k1_xboole_0
    | ~ spl6_10 ),
    inference(resolution,[],[f148,f130])).

fof(f145,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f68,f143])).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ~ r2_hidden(sK2,sK1)
    & m1_connsp_2(sK1,sK0,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f56,f55,f54])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X2,X1)
                & m1_connsp_2(X1,X0,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,X1)
              & m1_connsp_2(X1,sK0,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,X1)
              & m1_connsp_2(X1,X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(X2,sK1)
            & m1_connsp_2(sK1,X0,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_connsp_2(X1,X0,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK2,X1)
        & m1_connsp_2(X1,X0,sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,X1)
              & m1_connsp_2(X1,X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,X1)
              & m1_connsp_2(X1,X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( m1_connsp_2(X1,X0,X2)
                 => r2_hidden(X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',t6_connsp_2)).

fof(f138,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f70,f136])).

fof(f70,plain,(
    m1_connsp_2(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f131,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f69,f129])).

fof(f69,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f57])).

fof(f124,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f71,f122])).

fof(f71,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f117,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f89,f115])).

fof(f115,plain,
    ( spl6_6
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f89,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f63])).

fof(f63,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK5) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t6_connsp_2.p',existence_l1_pre_topc)).

fof(f110,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f67,f108])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f103,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f66,f101])).

fof(f66,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f65,f94])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
