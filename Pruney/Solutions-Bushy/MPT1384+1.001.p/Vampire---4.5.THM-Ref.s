%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1384+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 707 expanded)
%              Number of leaves         :   15 ( 153 expanded)
%              Depth                    :   23
%              Number of atoms          :  730 (4185 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1555,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f688,f1000,f1004,f1554])).

fof(f1554,plain,
    ( spl10_1
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f1553])).

fof(f1553,plain,
    ( $false
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1551,f1262])).

fof(f1262,plain,
    ( ~ r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK1)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1261,f69])).

fof(f69,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f67])).

% (13181)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
fof(f67,plain,
    ( spl10_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f1261,plain,
    ( ~ r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK1)
    | v3_pre_topc(sK1,sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1260,f114])).

fof(f114,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl10_7
  <=> r2_hidden(sK5(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f1260,plain,
    ( ~ r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK1)
    | ~ r2_hidden(sK5(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1259,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_tarski(X3,X1)
                              & m1_connsp_2(X3,X0,X2) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f1259,plain,
    ( ~ r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ r2_hidden(sK5(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1258,f1138])).

fof(f1138,plain,
    ( v3_pre_topc(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1137,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1137,plain,
    ( v3_pre_topc(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1136,f1045])).

fof(f1045,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_7 ),
    inference(resolution,[],[f1010,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f1010,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | m1_subset_1(sK5(sK0,sK1),X0) )
    | ~ spl10_7 ),
    inference(resolution,[],[f114,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f1136,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v3_pre_topc(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1135,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1135,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v3_pre_topc(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1121,f37])).

fof(f1121,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v3_pre_topc(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(resolution,[],[f1051,f242])).

fof(f242,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f40,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

% (13172)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f1051,plain,
    ( m1_connsp_2(sK3(sK5(sK0,sK1)),sK0,sK5(sK0,sK1))
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1047,f114])).

fof(f1047,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | m1_connsp_2(sK3(sK5(sK0,sK1)),sK0,sK5(sK0,sK1))
    | spl10_1
    | ~ spl10_7 ),
    inference(resolution,[],[f1045,f813])).

fof(f813,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1)
        | m1_connsp_2(sK3(X2),sK0,X2) )
    | spl10_1 ),
    inference(subsumption_resolution,[],[f30,f69])).

fof(f30,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | m1_connsp_2(sK3(X2),sK0,X2)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1258,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK0)
    | ~ r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ r2_hidden(sK5(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1257,f1126])).

fof(f1126,plain,
    ( m1_subset_1(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1125,f36])).

fof(f1125,plain,
    ( m1_subset_1(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1124,f1045])).

fof(f1124,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1123,f38])).

fof(f1123,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1118,f37])).

fof(f1118,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(resolution,[],[f1051,f597])).

fof(f597,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f39,f56])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1257,plain,
    ( ~ m1_subset_1(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK0)
    | ~ r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ r2_hidden(sK5(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1256,f35])).

fof(f1256,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK0)
    | ~ r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ r2_hidden(sK5(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1252,f38])).

% (13191)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
fof(f1252,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK0)
    | ~ r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ r2_hidden(sK5(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(resolution,[],[f1130,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X3)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X1)
      | ~ v2_pre_topc(X0)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tops_1)).

fof(f1130,plain,
    ( r2_hidden(sK5(sK0,sK1),sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))))
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1129,f36])).

fof(f1129,plain,
    ( r2_hidden(sK5(sK0,sK1),sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))))
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1128,f1045])).

fof(f1128,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(sK5(sK0,sK1),sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))))
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1127,f38])).

fof(f1127,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(sK5(sK0,sK1),sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))))
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1119,f37])).

fof(f1119,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(sK5(sK0,sK1),sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))))
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(resolution,[],[f1051,f454])).

fof(f454,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X1,sK4(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f42,f56])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,sK4(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1551,plain,
    ( r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK1)
    | spl10_1
    | ~ spl10_7 ),
    inference(resolution,[],[f1325,f1052])).

fof(f1052,plain,
    ( r1_tarski(sK3(sK5(sK0,sK1)),sK1)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1048,f114])).

fof(f1048,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | r1_tarski(sK3(sK5(sK0,sK1)),sK1)
    | spl10_1
    | ~ spl10_7 ),
    inference(resolution,[],[f1045,f703])).

fof(f703,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1)
        | r1_tarski(sK3(X2),sK1) )
    | spl10_1 ),
    inference(subsumption_resolution,[],[f31,f69])).

fof(f31,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | r1_tarski(sK3(X2),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1325,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3(sK5(sK0,sK1)),X0)
        | r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),X0) )
    | spl10_1
    | ~ spl10_7 ),
    inference(resolution,[],[f1134,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1134,plain,
    ( r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK3(sK5(sK0,sK1)))
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1133,f36])).

fof(f1133,plain,
    ( r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK3(sK5(sK0,sK1)))
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1132,f1045])).

fof(f1132,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK3(sK5(sK0,sK1)))
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1131,f38])).

fof(f1131,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK3(sK5(sK0,sK1)))
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1120,f37])).

fof(f1120,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | r1_tarski(sK4(sK0,sK5(sK0,sK1),sK3(sK5(sK0,sK1))),sK3(sK5(sK0,sK1)))
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(resolution,[],[f1051,f414])).

% (13181)Refutation not found, incomplete strategy% (13181)------------------------------
% (13181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13181)Termination reason: Refutation not found, incomplete strategy

% (13181)Memory used [KB]: 9850
% (13181)Time elapsed: 0.081 s
% (13181)------------------------------
% (13181)------------------------------
fof(f414,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_tarski(sK4(X0,X1,X2),X2)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f41,f56])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK4(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1004,plain,
    ( ~ spl10_10
    | spl10_1
    | spl10_7 ),
    inference(avatar_split_clause,[],[f1003,f112,f67,f154])).

fof(f154,plain,
    ( spl10_10
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f1003,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_1
    | spl10_7 ),
    inference(subsumption_resolution,[],[f711,f902])).

fof(f902,plain,
    ( ~ sP9(sK7(sK0,sK1))
    | spl10_1
    | spl10_7 ),
    inference(resolution,[],[f899,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP9(X1) ) ),
    inference(general_splitting,[],[f61,f64_D])).

fof(f64,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP9(X1) ) ),
    inference(cnf_transformation,[],[f64_D])).

fof(f64_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP9(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f899,plain,
    ( r2_hidden(sK5(sK0,sK1),sK7(sK0,sK1))
    | spl10_1
    | spl10_7 ),
    inference(subsumption_resolution,[],[f205,f69])).

fof(f205,plain,
    ( r2_hidden(sK5(sK0,sK1),sK7(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f204,f113])).

fof(f113,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f204,plain,
    ( r2_hidden(sK5(sK0,sK1),sK7(sK0,sK1))
    | r2_hidden(sK5(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f203,f37])).

fof(f203,plain,
    ( ~ v2_pre_topc(sK0)
    | r2_hidden(sK5(sK0,sK1),sK7(sK0,sK1))
    | r2_hidden(sK5(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f202,f38])).

fof(f202,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r2_hidden(sK5(sK0,sK1),sK7(sK0,sK1))
    | r2_hidden(sK5(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f49,f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(sK5(X0,X1),sK7(X0,X1))
      | r2_hidden(sK5(X0,X1),X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f711,plain,
    ( ~ v1_xboole_0(sK1)
    | sP9(sK7(sK0,sK1))
    | spl10_1
    | spl10_7 ),
    inference(resolution,[],[f706,f64])).

fof(f706,plain,
    ( m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(sK1))
    | spl10_1
    | spl10_7 ),
    inference(resolution,[],[f704,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f704,plain,
    ( r1_tarski(sK7(sK0,sK1),sK1)
    | spl10_1
    | spl10_7 ),
    inference(subsumption_resolution,[],[f251,f69])).

fof(f251,plain,
    ( r1_tarski(sK7(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f122,f113])).

fof(f122,plain,
    ( r1_tarski(sK7(sK0,sK1),sK1)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f121,f37])).

fof(f121,plain,
    ( ~ v2_pre_topc(sK0)
    | r1_tarski(sK7(sK0,sK1),sK1)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f120,f38])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK7(sK0,sK1),sK1)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f48,f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r1_tarski(sK7(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1000,plain,
    ( spl10_1
    | spl10_7
    | spl10_10 ),
    inference(avatar_contradiction_clause,[],[f999])).

fof(f999,plain,
    ( $false
    | spl10_1
    | spl10_7
    | spl10_10 ),
    inference(subsumption_resolution,[],[f998,f113])).

fof(f998,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | spl10_1
    | spl10_7
    | spl10_10 ),
    inference(subsumption_resolution,[],[f997,f156])).

fof(f156,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f997,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | spl10_1
    | spl10_7 ),
    inference(resolution,[],[f995,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f995,plain,
    ( m1_subset_1(sK5(sK0,sK1),sK1)
    | spl10_1
    | spl10_7 ),
    inference(resolution,[],[f900,f706])).

fof(f900,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(X0))
        | m1_subset_1(sK5(sK0,sK1),X0) )
    | spl10_1
    | spl10_7 ),
    inference(resolution,[],[f899,f60])).

fof(f688,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f687])).

fof(f687,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f678,f324])).

fof(f324,plain,
    ( ~ m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f323,f274])).

fof(f274,plain,
    ( r1_tarski(sK6(sK0,sK1,sK2),sK1)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f273,f73])).

fof(f73,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl10_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f273,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(sK6(sK0,sK1,X0),sK1) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f255,f68])).

fof(f68,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f255,plain,(
    ! [X0] :
      ( r1_tarski(sK6(sK0,sK1,X0),sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f254,f37])).

fof(f254,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | r1_tarski(sK6(sK0,sK1,X0),sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f105,f38])).

fof(f105,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | r1_tarski(sK6(sK0,sK1,X0),sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f52,f35])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r1_tarski(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f323,plain,
    ( ~ m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2)
    | ~ r1_tarski(sK6(sK0,sK1,sK2),sK1)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f281,f285])).

fof(f285,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f283,f57])).

fof(f283,plain,
    ( r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f275,f78])).

fof(f78,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f58,f35])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK6(sK0,sK1,sK2),X0) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f274,f59])).

fof(f281,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X3,sK0,sK2)
        | ~ r1_tarski(X3,sK1) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f32,f68])).

fof(f32,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X3,sK0,sK2)
      | ~ r1_tarski(X3,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f678,plain,
    ( m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f518,f269])).

fof(f269,plain,
    ( r2_hidden(sK2,sK6(sK0,sK1,sK2))
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f268,f73])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK6(sK0,sK1,X0)) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f253,f68])).

fof(f253,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK6(sK0,sK1,X0))
      | ~ r2_hidden(X0,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f252,f37])).

fof(f252,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | r2_hidden(X0,sK6(sK0,sK1,X0))
      | ~ r2_hidden(X0,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f106,f38])).

fof(f106,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | r2_hidden(X0,sK6(sK0,sK1,X0))
      | ~ r2_hidden(X0,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f53,f35])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X2,sK6(X0,X1,X2))
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f518,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK6(sK0,sK1,sK2))
        | m1_connsp_2(sK6(sK0,sK1,sK2),sK0,X1) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f517,f340])).

fof(f340,plain,
    ( v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f339,f73])).

fof(f339,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | v3_pre_topc(sK6(sK0,sK1,X0),sK0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f257,f68])).

fof(f257,plain,(
    ! [X0] :
      ( v3_pre_topc(sK6(sK0,sK1,X0),sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f256,f37])).

fof(f256,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v3_pre_topc(sK6(sK0,sK1,X0),sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f104,f38])).

fof(f104,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v3_pre_topc(sK6(sK0,sK1,X0),sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f51,f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f517,plain,
    ( ! [X1] :
        ( ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
        | ~ r2_hidden(X1,sK6(sK0,sK1,sK2))
        | m1_connsp_2(sK6(sK0,sK1,sK2),sK0,X1) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f516,f36])).

fof(f516,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
        | ~ r2_hidden(X1,sK6(sK0,sK1,sK2))
        | m1_connsp_2(sK6(sK0,sK1,sK2),sK0,X1) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f515,f38])).

fof(f515,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
        | ~ r2_hidden(X1,sK6(sK0,sK1,sK2))
        | m1_connsp_2(sK6(sK0,sK1,sK2),sK0,X1) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f510,f37])).

fof(f510,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
        | ~ r2_hidden(X1,sK6(sK0,sK1,sK2))
        | m1_connsp_2(sK6(sK0,sK1,sK2),sK0,X1) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f485,f285])).

fof(f485,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(subsumption_resolution,[],[f44,f60])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f74,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f34,f71,f67])).

fof(f34,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
