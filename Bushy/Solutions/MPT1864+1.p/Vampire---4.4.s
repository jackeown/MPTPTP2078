%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t32_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:31 EDT 2019

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 175 expanded)
%              Number of leaves         :   18 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  315 ( 641 expanded)
%              Number of equality atoms :   18 (  45 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7892,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f108,f112,f126,f135,f169,f186,f257,f373,f1385,f3093,f7811,f7891])).

fof(f7891,plain,
    ( spl8_256
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f720,f371,f167,f133,f110,f97,f7429])).

fof(f7429,plain,
    ( spl8_256
  <=> m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_256])])).

fof(f97,plain,
    ( spl8_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f110,plain,
    ( spl8_6
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f133,plain,
    ( spl8_14
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f167,plain,
    ( spl8_18
  <=> r1_tarski(k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f371,plain,
    ( spl8_50
  <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f720,plain,
    ( m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f703,f168])).

fof(f168,plain,
    ( r1_tarski(k1_tarski(sK2),sK1)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f167])).

fof(f703,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK1)
    | m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_50 ),
    inference(resolution,[],[f372,f153])).

fof(f153,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,sK1)
        | m1_subset_1(sK4(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f152,f111])).

fof(f111,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f152,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,sK1)
        | m1_subset_1(sK4(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl8_0
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f141,f98])).

fof(f98,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f97])).

fof(f141,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,sK1)
        | m1_subset_1(sK4(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl8_14 ),
    inference(resolution,[],[f134,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t32_tex_2.p',d5_tex_2)).

fof(f134,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f372,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f371])).

fof(f7811,plain,
    ( ~ spl8_120
    | ~ spl8_168
    | ~ spl8_256 ),
    inference(avatar_contradiction_clause,[],[f7810])).

fof(f7810,plain,
    ( $false
    | ~ spl8_120
    | ~ spl8_168
    | ~ spl8_256 ),
    inference(subsumption_resolution,[],[f7809,f3092])).

fof(f3092,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_tarski(sK2))) = k1_tarski(sK2)
    | ~ spl8_168 ),
    inference(avatar_component_clause,[],[f3091])).

fof(f3091,plain,
    ( spl8_168
  <=> k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_tarski(sK2))) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_168])])).

fof(f7809,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_tarski(sK2))) != k1_tarski(sK2)
    | ~ spl8_120
    | ~ spl8_256 ),
    inference(subsumption_resolution,[],[f7785,f1384])).

fof(f1384,plain,
    ( v3_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0)
    | ~ spl8_120 ),
    inference(avatar_component_clause,[],[f1383])).

fof(f1383,plain,
    ( spl8_120
  <=> v3_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_120])])).

fof(f7785,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_tarski(sK2))) != k1_tarski(sK2)
    | ~ spl8_256 ),
    inference(resolution,[],[f7430,f59])).

fof(f59,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                              & v3_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t32_tex_2.p',t32_tex_2)).

fof(f7430,plain,
    ( m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_256 ),
    inference(avatar_component_clause,[],[f7429])).

fof(f3093,plain,
    ( spl8_168
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f719,f371,f167,f133,f110,f97,f3091])).

fof(f719,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_tarski(sK2))) = k1_tarski(sK2)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f702,f168])).

fof(f702,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK1)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_tarski(sK2))) = k1_tarski(sK2)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_50 ),
    inference(resolution,[],[f372,f157])).

fof(f157,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3 )
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f156,f111])).

fof(f156,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl8_0
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f143,f98])).

fof(f143,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl8_14 ),
    inference(resolution,[],[f134,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1385,plain,
    ( spl8_120
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f722,f371,f167,f133,f110,f97,f1383])).

fof(f722,plain,
    ( v3_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f704,f168])).

fof(f704,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK1)
    | v3_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_50 ),
    inference(resolution,[],[f372,f155])).

fof(f155,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X2,sK1)
        | v3_pre_topc(sK4(sK0,sK1,X2),sK0) )
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f154,f111])).

fof(f154,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X2,sK1)
        | v3_pre_topc(sK4(sK0,sK1,X2),sK0)
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl8_0
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f142,f98])).

fof(f142,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X2,sK1)
        | v3_pre_topc(sK4(sK0,sK1,X2),sK0)
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl8_14 ),
    inference(resolution,[],[f134,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f373,plain,
    ( spl8_50
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f302,f255,f371])).

fof(f255,plain,
    ( spl8_34
  <=> r1_tarski(k1_tarski(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f302,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_34 ),
    inference(resolution,[],[f256,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t32_tex_2.p',t3_subset)).

fof(f256,plain,
    ( r1_tarski(k1_tarski(sK2),u1_struct_0(sK0))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f255])).

fof(f257,plain,
    ( spl8_34
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f192,f184,f255])).

fof(f184,plain,
    ( spl8_24
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f192,plain,
    ( r1_tarski(k1_tarski(sK2),u1_struct_0(sK0))
    | ~ spl8_24 ),
    inference(resolution,[],[f185,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t32_tex_2.p',t37_zfmisc_1)).

fof(f185,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f184])).

fof(f186,plain,
    ( spl8_24
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f178,f133,f124,f106,f184])).

fof(f106,plain,
    ( spl8_4
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f124,plain,
    ( spl8_10
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f178,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f127,f177])).

fof(f177,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_4
    | ~ spl8_14 ),
    inference(resolution,[],[f117,f134])).

fof(f117,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl8_4 ),
    inference(resolution,[],[f107,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t32_tex_2.p',t5_subset)).

fof(f107,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f127,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl8_10 ),
    inference(resolution,[],[f125,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t32_tex_2.p',t2_subset)).

fof(f125,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f169,plain,
    ( spl8_18
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f118,f106,f167])).

fof(f118,plain,
    ( r1_tarski(k1_tarski(sK2),sK1)
    | ~ spl8_4 ),
    inference(resolution,[],[f107,f68])).

fof(f135,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f62,f133])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f126,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f60,f124])).

fof(f60,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f112,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f63,f110])).

fof(f63,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f108,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f61,f106])).

fof(f61,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f99,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f64,f97])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
