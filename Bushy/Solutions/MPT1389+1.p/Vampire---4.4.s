%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t14_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:52 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 312 expanded)
%              Number of leaves         :   30 ( 123 expanded)
%              Depth                    :   12
%              Number of atoms          :  587 (1178 expanded)
%              Number of equality atoms :   28 (  75 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f866,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f126,f130,f135,f139,f158,f162,f166,f170,f221,f230,f270,f278,f328,f349,f410,f443,f573,f853,f865])).

fof(f865,plain,
    ( ~ spl10_6
    | ~ spl10_14
    | spl10_27
    | ~ spl10_52
    | ~ spl10_112
    | ~ spl10_182 ),
    inference(avatar_contradiction_clause,[],[f864])).

fof(f864,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_27
    | ~ spl10_52
    | ~ spl10_112
    | ~ spl10_182 ),
    inference(subsumption_resolution,[],[f863,f229])).

fof(f229,plain,
    ( ~ r1_tarski(k1_connsp_1(sK1,sK2),k1_connsp_1(sK0,sK2))
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl10_27
  <=> ~ r1_tarski(k1_connsp_1(sK1,sK2),k1_connsp_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f863,plain,
    ( r1_tarski(k1_connsp_1(sK1,sK2),k1_connsp_1(sK0,sK2))
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_52
    | ~ spl10_112
    | ~ spl10_182 ),
    inference(forward_demodulation,[],[f862,f602])).

fof(f602,plain,
    ( k1_connsp_1(sK0,sK2) = k3_tarski(sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_52
    | ~ spl10_112 ),
    inference(forward_demodulation,[],[f598,f364])).

fof(f364,plain,
    ( k1_connsp_1(sK0,sK2) = k5_setfam_1(u1_struct_0(sK0),sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f363,f129])).

fof(f129,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl10_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f363,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_connsp_1(sK0,sK2) = k5_setfam_1(u1_struct_0(sK0),sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ spl10_14
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f356,f161])).

fof(f161,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl10_14
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f356,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | k1_connsp_1(sK0,sK2) = k5_setfam_1(u1_struct_0(sK0),sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ spl10_52 ),
    inference(resolution,[],[f327,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | k1_connsp_1(X0,X1) = k5_setfam_1(u1_struct_0(X0),sK4(X0,X1,k1_connsp_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k5_setfam_1(u1_struct_0(X0),sK4(X0,X1,X2)) = X2
      | k1_connsp_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_1(X0,X1) = X2
              <=> ? [X3] :
                    ( k5_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v2_connsp_1(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k1_connsp_1(X0,X1) = X2
              <=> ? [X3] :
                    ( k5_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v2_connsp_1(X4,X0) ) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t14_connsp_2.p',d7_connsp_1)).

fof(f327,plain,
    ( m1_subset_1(k1_connsp_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl10_52
  <=> m1_subset_1(k1_connsp_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f598,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK4(sK0,sK2,k1_connsp_1(sK0,sK2))) = k3_tarski(sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ spl10_112 ),
    inference(resolution,[],[f572,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t14_connsp_2.p',redefinition_k5_setfam_1)).

fof(f572,plain,
    ( m1_subset_1(sK4(sK0,sK2,k1_connsp_1(sK0,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_112 ),
    inference(avatar_component_clause,[],[f571])).

fof(f571,plain,
    ( spl10_112
  <=> m1_subset_1(sK4(sK0,sK2,k1_connsp_1(sK0,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_112])])).

fof(f862,plain,
    ( r1_tarski(k1_connsp_1(sK1,sK2),k3_tarski(sK4(sK0,sK2,k1_connsp_1(sK0,sK2))))
    | ~ spl10_182 ),
    inference(resolution,[],[f852,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t14_connsp_2.p',t92_zfmisc_1)).

fof(f852,plain,
    ( r2_hidden(k1_connsp_1(sK1,sK2),sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ spl10_182 ),
    inference(avatar_component_clause,[],[f851])).

fof(f851,plain,
    ( spl10_182
  <=> r2_hidden(k1_connsp_1(sK1,sK2),sK4(sK0,sK2,k1_connsp_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_182])])).

fof(f853,plain,
    ( spl10_182
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_38
    | ~ spl10_52
    | ~ spl10_72
    | ~ spl10_84 ),
    inference(avatar_split_clause,[],[f845,f441,f408,f326,f268,f160,f128,f851])).

fof(f268,plain,
    ( spl10_38
  <=> r2_hidden(sK2,k1_connsp_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f408,plain,
    ( spl10_72
  <=> v2_connsp_1(k1_connsp_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f441,plain,
    ( spl10_84
  <=> m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f845,plain,
    ( r2_hidden(k1_connsp_1(sK1,sK2),sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_38
    | ~ spl10_52
    | ~ spl10_72
    | ~ spl10_84 ),
    inference(subsumption_resolution,[],[f672,f844])).

fof(f844,plain,
    ( sP6(k1_connsp_1(sK1,sK2),sK2,sK0)
    | ~ spl10_38
    | ~ spl10_72 ),
    inference(resolution,[],[f414,f269])).

fof(f269,plain,
    ( r2_hidden(sK2,k1_connsp_1(sK1,sK2))
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f268])).

fof(f414,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_connsp_1(sK1,sK2))
        | sP6(k1_connsp_1(sK1,sK2),X0,sK0) )
    | ~ spl10_72 ),
    inference(resolution,[],[f409,f78])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( ~ v2_connsp_1(X4,X0)
      | ~ r2_hidden(X1,X4)
      | sP6(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f409,plain,
    ( v2_connsp_1(k1_connsp_1(sK1,sK2),sK0)
    | ~ spl10_72 ),
    inference(avatar_component_clause,[],[f408])).

fof(f672,plain,
    ( ~ sP6(k1_connsp_1(sK1,sK2),sK2,sK0)
    | r2_hidden(k1_connsp_1(sK1,sK2),sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_52
    | ~ spl10_84 ),
    inference(resolution,[],[f360,f442])).

fof(f442,plain,
    ( m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_84 ),
    inference(avatar_component_clause,[],[f441])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sP6(X0,sK2,sK0)
        | r2_hidden(X0,sK4(sK0,sK2,k1_connsp_1(sK0,sK2))) )
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f359,f129])).

fof(f359,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sP6(X0,sK2,sK0)
        | r2_hidden(X0,sK4(sK0,sK2,k1_connsp_1(sK0,sK2))) )
    | ~ spl10_14
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f354,f161])).

fof(f354,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sP6(X0,sK2,sK0)
        | r2_hidden(X0,sK4(sK0,sK2,k1_connsp_1(sK0,sK2))) )
    | ~ spl10_52 ),
    inference(resolution,[],[f327,f111])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP6(X4,X1,X0)
      | r2_hidden(X4,sK4(X0,X1,k1_connsp_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP6(X4,X1,X0)
      | r2_hidden(X4,sK4(X0,X1,X2))
      | k1_connsp_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f573,plain,
    ( spl10_112
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_52 ),
    inference(avatar_split_clause,[],[f362,f326,f160,f128,f571])).

fof(f362,plain,
    ( m1_subset_1(sK4(sK0,sK2,k1_connsp_1(sK0,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f361,f129])).

fof(f361,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK4(sK0,sK2,k1_connsp_1(sK0,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_14
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f355,f161])).

fof(f355,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK4(sK0,sK2,k1_connsp_1(sK0,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_52 ),
    inference(resolution,[],[f327,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1,k1_connsp_1(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | k1_connsp_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f443,plain,
    ( spl10_84
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_60 ),
    inference(avatar_split_clause,[],[f381,f347,f137,f128,f441])).

fof(f137,plain,
    ( spl10_10
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f347,plain,
    ( spl10_60
  <=> m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f381,plain,
    ( m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_60 ),
    inference(resolution,[],[f148,f348])).

fof(f348,plain,
    ( m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_60 ),
    inference(avatar_component_clause,[],[f347])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_6
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f142,f129])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_10 ),
    inference(resolution,[],[f138,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t14_connsp_2.p',t39_pre_topc)).

fof(f138,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f410,plain,
    ( spl10_72
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_42
    | ~ spl10_60 ),
    inference(avatar_split_clause,[],[f384,f347,f276,f137,f128,f124,f408])).

fof(f124,plain,
    ( spl10_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f276,plain,
    ( spl10_42
  <=> v2_connsp_1(k1_connsp_1(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f384,plain,
    ( v2_connsp_1(k1_connsp_1(sK1,sK2),sK0)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_42
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f383,f277])).

fof(f277,plain,
    ( v2_connsp_1(k1_connsp_1(sK1,sK2),sK1)
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f276])).

fof(f383,plain,
    ( ~ v2_connsp_1(k1_connsp_1(sK1,sK2),sK1)
    | v2_connsp_1(k1_connsp_1(sK1,sK2),sK0)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_60 ),
    inference(resolution,[],[f151,f348])).

fof(f151,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_connsp_1(X1,sK1)
        | v2_connsp_1(X1,sK0) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f150,f148])).

fof(f150,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_connsp_1(X1,sK1)
        | v2_connsp_1(X1,sK0) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f149,f125])).

fof(f125,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f149,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_connsp_1(X1,sK1)
        | v2_connsp_1(X1,sK0) )
    | ~ spl10_6
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f143,f129])).

fof(f143,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_connsp_1(X1,sK1)
        | v2_connsp_1(X1,sK0) )
    | ~ spl10_10 ),
    inference(resolution,[],[f138,f113])).

fof(f113,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_connsp_1(X3,X1)
      | v2_connsp_1(X3,X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X2 != X3
      | ~ v2_connsp_1(X3,X1)
      | v2_connsp_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_connsp_1(X2,X0)
                  <=> v2_connsp_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_connsp_1(X2,X0)
                  <=> v2_connsp_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_connsp_1(X2,X0)
                    <=> v2_connsp_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t14_connsp_2.p',t24_connsp_1)).

fof(f349,plain,
    ( spl10_60
    | ~ spl10_12
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f213,f168,f156,f347])).

fof(f156,plain,
    ( spl10_12
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f168,plain,
    ( spl10_18
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f213,plain,
    ( m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_12
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f198,f157])).

fof(f157,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f156])).

fof(f198,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_18 ),
    inference(resolution,[],[f169,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t14_connsp_2.p',dt_k1_connsp_1)).

fof(f169,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f328,plain,
    ( spl10_52
    | ~ spl10_6
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f192,f160,f128,f326])).

fof(f192,plain,
    ( m1_subset_1(k1_connsp_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_6
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f177,f129])).

fof(f177,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_connsp_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_14 ),
    inference(resolution,[],[f161,f74])).

fof(f278,plain,
    ( spl10_42
    | spl10_1
    | ~ spl10_12
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f212,f168,f164,f156,f116,f276])).

fof(f116,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f164,plain,
    ( spl10_16
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f212,plain,
    ( v2_connsp_1(k1_connsp_1(sK1,sK2),sK1)
    | ~ spl10_1
    | ~ spl10_12
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f211,f117])).

fof(f117,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f211,plain,
    ( v2_struct_0(sK1)
    | v2_connsp_1(k1_connsp_1(sK1,sK2),sK1)
    | ~ spl10_12
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f210,f157])).

fof(f210,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v2_connsp_1(k1_connsp_1(sK1,sK2),sK1)
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f197,f165])).

fof(f165,plain,
    ( v2_pre_topc(sK1)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f164])).

fof(f197,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v2_connsp_1(k1_connsp_1(sK1,sK2),sK1)
    | ~ spl10_18 ),
    inference(resolution,[],[f169,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_connsp_1(k1_connsp_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_connsp_1(k1_connsp_1(X0,X1),X0)
        & ~ v1_xboole_0(k1_connsp_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_connsp_1(k1_connsp_1(X0,X1),X0)
        & ~ v1_xboole_0(k1_connsp_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_connsp_1(k1_connsp_1(X0,X1),X0)
        & ~ v1_xboole_0(k1_connsp_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t14_connsp_2.p',fc2_connsp_1)).

fof(f270,plain,
    ( spl10_38
    | spl10_1
    | ~ spl10_12
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f206,f168,f164,f156,f116,f268])).

fof(f206,plain,
    ( r2_hidden(sK2,k1_connsp_1(sK1,sK2))
    | ~ spl10_1
    | ~ spl10_12
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f205,f117])).

fof(f205,plain,
    ( v2_struct_0(sK1)
    | r2_hidden(sK2,k1_connsp_1(sK1,sK2))
    | ~ spl10_12
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f204,f157])).

fof(f204,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r2_hidden(sK2,k1_connsp_1(sK1,sK2))
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f195,f165])).

fof(f195,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r2_hidden(sK2,k1_connsp_1(sK1,sK2))
    | ~ spl10_18 ),
    inference(resolution,[],[f169,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_connsp_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_1(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_1(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t14_connsp_2.p',t40_connsp_1)).

fof(f230,plain,
    ( ~ spl10_27
    | ~ spl10_8
    | spl10_23 ),
    inference(avatar_split_clause,[],[f222,f219,f133,f228])).

fof(f133,plain,
    ( spl10_8
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f219,plain,
    ( spl10_23
  <=> ~ r1_tarski(k1_connsp_1(sK1,sK3),k1_connsp_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f222,plain,
    ( ~ r1_tarski(k1_connsp_1(sK1,sK2),k1_connsp_1(sK0,sK2))
    | ~ spl10_8
    | ~ spl10_23 ),
    inference(forward_demodulation,[],[f220,f134])).

fof(f134,plain,
    ( sK2 = sK3
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f220,plain,
    ( ~ r1_tarski(k1_connsp_1(sK1,sK3),k1_connsp_1(sK0,sK2))
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f219])).

fof(f221,plain,(
    ~ spl10_23 ),
    inference(avatar_split_clause,[],[f64,f219])).

fof(f64,plain,(
    ~ r1_tarski(k1_connsp_1(sK1,sK3),k1_connsp_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2))
                  & X2 = X3
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2))
                  & X2 = X3
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
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
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ( X2 = X3
                     => r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2)) ) ) ) ) ) ),
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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( X2 = X3
                   => r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t14_connsp_2.p',t14_connsp_2)).

fof(f170,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f114,f168])).

fof(f114,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f62,f63])).

fof(f63,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f166,plain,
    ( spl10_16
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f147,f137,f128,f124,f164])).

fof(f147,plain,
    ( v2_pre_topc(sK1)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f146,f125])).

fof(f146,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK1)
    | ~ spl10_6
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f141,f129])).

fof(f141,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK1)
    | ~ spl10_10 ),
    inference(resolution,[],[f138,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t14_connsp_2.p',cc1_pre_topc)).

fof(f162,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f65,f160])).

fof(f65,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f158,plain,
    ( spl10_12
    | ~ spl10_6
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f145,f137,f128,f156])).

fof(f145,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_6
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f140,f129])).

fof(f140,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl10_10 ),
    inference(resolution,[],[f138,f97])).

fof(f97,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t14_connsp_2.p',dt_m1_pre_topc)).

fof(f139,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f67,f137])).

fof(f67,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f135,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f63,f133])).

fof(f130,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f70,f128])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f126,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f69,f124])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f118,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f66,f116])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
