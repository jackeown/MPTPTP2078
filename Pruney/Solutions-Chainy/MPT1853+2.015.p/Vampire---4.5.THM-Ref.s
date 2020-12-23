%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 241 expanded)
%              Number of leaves         :   39 ( 110 expanded)
%              Depth                    :    8
%              Number of atoms          :  459 ( 738 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f492,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f102,f111,f112,f118,f185,f207,f217,f225,f231,f237,f246,f248,f290,f298,f311,f314,f327,f432,f475,f476,f478,f481])).

fof(f481,plain,
    ( ~ spl6_28
    | spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f340,f108,f115,f99,f94,f295])).

fof(f295,plain,
    ( spl6_28
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f94,plain,
    ( spl6_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f99,plain,
    ( spl6_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f115,plain,
    ( spl6_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f108,plain,
    ( spl6_5
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f340,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f109,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

% (18895)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f109,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f478,plain,
    ( u1_struct_0(sK0) != sK3(sK0,k1_tex_2(sK0,sK1))
    | u1_struct_0(k1_tex_2(sK0,sK1)) != sK3(sK0,k1_tex_2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f476,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) != sK3(sK0,k1_tex_2(sK0,sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f475,plain,
    ( spl6_4
    | ~ spl6_1
    | ~ spl6_16
    | ~ spl6_52
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f460,f234,f472,f222,f89,f104])).

fof(f104,plain,
    ( spl6_4
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f89,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f222,plain,
    ( spl6_16
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f472,plain,
    ( spl6_52
  <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f234,plain,
    ( spl6_18
  <=> u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f460,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl6_18 ),
    inference(superposition,[],[f64,f236])).

fof(f236,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f234])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f432,plain,
    ( spl6_43
    | spl6_44
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f411,f287,f429,f425])).

fof(f425,plain,
    ( spl6_43
  <=> v1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f429,plain,
    ( spl6_44
  <=> u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f287,plain,
    ( spl6_27
  <=> m1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f411,plain,
    ( u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1))
    | v1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl6_27 ),
    inference(resolution,[],[f289,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f289,plain,
    ( m1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f287])).

fof(f327,plain,
    ( ~ spl6_9
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(resolution,[],[f137,f212])).

fof(f212,plain,
    ( v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl6_14
  <=> v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f137,plain,
    ( ! [X0] : ~ v1_zfmisc_1(X0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_9
  <=> ! [X0] : ~ v1_zfmisc_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f314,plain,
    ( spl6_28
    | ~ spl6_6
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f312,f243,f115,f295])).

fof(f243,plain,
    ( spl6_20
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f312,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ spl6_20 ),
    inference(resolution,[],[f245,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f245,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f243])).

fof(f311,plain,
    ( spl6_20
    | spl6_9
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f307,f239,f136,f243])).

fof(f239,plain,
    ( spl6_19
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f307,plain,
    ( ! [X3] :
        ( ~ v1_zfmisc_1(X3)
        | v1_zfmisc_1(u1_struct_0(sK0)) )
    | ~ spl6_19 ),
    inference(resolution,[],[f300,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_zfmisc_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_zfmisc_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_1)).

fof(f300,plain,
    ( ! [X1] : m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X1))
    | ~ spl6_19 ),
    inference(resolution,[],[f291,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f291,plain,
    ( ! [X0] : r1_tarski(u1_struct_0(sK0),X0)
    | ~ spl6_19 ),
    inference(resolution,[],[f241,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f80,f72])).

% (18871)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f241,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f239])).

fof(f298,plain,
    ( spl6_2
    | spl6_12
    | ~ spl6_16
    | ~ spl6_1
    | ~ spl6_28
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f293,f104,f295,f89,f222,f182,f94])).

fof(f182,plain,
    ( spl6_12
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f293,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f105,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | ~ v7_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f105,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f290,plain,
    ( spl6_4
    | spl6_27
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f285,f222,f89,f287,f104])).

fof(f285,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl6_16 ),
    inference(resolution,[],[f62,f224])).

fof(f224,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f222])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f248,plain,
    ( spl6_15
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f247,f228,f214])).

fof(f214,plain,
    ( spl6_15
  <=> l1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f228,plain,
    ( spl6_17
  <=> l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f247,plain,
    ( l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl6_17 ),
    inference(resolution,[],[f230,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f230,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f228])).

fof(f246,plain,
    ( spl6_5
    | spl6_19
    | spl6_20
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f174,f99,f243,f239,f108])).

fof(f174,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(resolution,[],[f66,f101])).

fof(f101,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | v1_subset_1(k6_domain_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

% (18872)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f237,plain,
    ( spl6_4
    | spl6_18
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f232,f222,f89,f234,f104])).

fof(f232,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl6_16 ),
    inference(resolution,[],[f63,f224])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f231,plain,
    ( spl6_17
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f226,f222,f89,f228])).

fof(f226,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl6_16 ),
    inference(resolution,[],[f224,f60])).

% (18875)Refutation not found, incomplete strategy% (18875)------------------------------
% (18875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18875)Termination reason: Refutation not found, incomplete strategy

% (18875)Memory used [KB]: 6268
% (18875)Time elapsed: 0.109 s
% (18875)------------------------------
% (18875)------------------------------
fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f225,plain,
    ( spl6_16
    | spl6_2
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f218,f99,f89,f94,f222])).

fof(f218,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f76,f101])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f217,plain,
    ( spl6_14
    | ~ spl6_15
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f208,f204,f214,f210])).

fof(f204,plain,
    ( spl6_13
  <=> v7_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f208,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl6_13 ),
    inference(resolution,[],[f206,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f206,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f204])).

% (18901)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f207,plain,
    ( spl6_13
    | spl6_2
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f200,f99,f89,f94,f204])).

fof(f200,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f78,f101])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v7_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f185,plain,
    ( ~ spl6_12
    | spl6_2
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f180,f99,f89,f94,f182])).

fof(f180,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f75,f101])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f118,plain,
    ( spl6_6
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f113,f89,f115])).

fof(f113,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f59,f91])).

fof(f91,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f112,plain,
    ( spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f50,f108,f104])).

fof(f50,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f111,plain,
    ( ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f51,f108,f104])).

fof(f51,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f102,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f52,f99])).

fof(f52,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f97,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f53,f94])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f92,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f54,f89])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (18894)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (18874)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (18885)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (18876)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (18882)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (18875)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (18887)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (18894)Refutation not found, incomplete strategy% (18894)------------------------------
% 0.20/0.52  % (18894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18894)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (18894)Memory used [KB]: 10746
% 0.20/0.52  % (18894)Time elapsed: 0.060 s
% 0.20/0.52  % (18894)------------------------------
% 0.20/0.52  % (18894)------------------------------
% 0.20/0.52  % (18880)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (18882)Refutation not found, incomplete strategy% (18882)------------------------------
% 0.20/0.52  % (18882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18882)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (18882)Memory used [KB]: 10618
% 0.20/0.52  % (18882)Time elapsed: 0.064 s
% 0.20/0.52  % (18882)------------------------------
% 0.20/0.52  % (18882)------------------------------
% 0.20/0.53  % (18900)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (18887)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (18877)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (18870)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (18870)Refutation not found, incomplete strategy% (18870)------------------------------
% 0.20/0.53  % (18870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (18870)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (18870)Memory used [KB]: 1663
% 0.20/0.53  % (18870)Time elapsed: 0.115 s
% 0.20/0.53  % (18870)------------------------------
% 0.20/0.53  % (18870)------------------------------
% 0.20/0.53  % (18884)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (18879)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (18898)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (18879)Refutation not found, incomplete strategy% (18879)------------------------------
% 0.20/0.54  % (18879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (18879)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (18879)Memory used [KB]: 10746
% 0.20/0.54  % (18879)Time elapsed: 0.127 s
% 0.20/0.54  % (18879)------------------------------
% 0.20/0.54  % (18879)------------------------------
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f492,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f92,f97,f102,f111,f112,f118,f185,f207,f217,f225,f231,f237,f246,f248,f290,f298,f311,f314,f327,f432,f475,f476,f478,f481])).
% 0.20/0.54  fof(f481,plain,(
% 0.20/0.54    ~spl6_28 | spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f340,f108,f115,f99,f94,f295])).
% 0.20/0.54  fof(f295,plain,(
% 0.20/0.54    spl6_28 <=> v7_struct_0(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    spl6_2 <=> v2_struct_0(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    spl6_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    spl6_6 <=> l1_struct_0(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    spl6_5 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.54  fof(f340,plain,(
% 0.20/0.54    ~l1_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v7_struct_0(sK0) | ~spl6_5),
% 0.20/0.54    inference(resolution,[],[f109,f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,axiom,(
% 0.20/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 0.20/0.54  % (18895)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl6_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f108])).
% 0.20/0.54  fof(f478,plain,(
% 0.20/0.54    u1_struct_0(sK0) != sK3(sK0,k1_tex_2(sK0,sK1)) | u1_struct_0(k1_tex_2(sK0,sK1)) != sK3(sK0,k1_tex_2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.20/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.54  fof(f476,plain,(
% 0.20/0.54    u1_struct_0(k1_tex_2(sK0,sK1)) != sK3(sK0,k1_tex_2(sK0,sK1)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.20/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.54  fof(f475,plain,(
% 0.20/0.54    spl6_4 | ~spl6_1 | ~spl6_16 | ~spl6_52 | ~spl6_18),
% 0.20/0.54    inference(avatar_split_clause,[],[f460,f234,f472,f222,f89,f104])).
% 0.20/0.54  fof(f104,plain,(
% 0.20/0.54    spl6_4 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    spl6_1 <=> l1_pre_topc(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.54  fof(f222,plain,(
% 0.20/0.54    spl6_16 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.54  fof(f472,plain,(
% 0.20/0.54    spl6_52 <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 0.20/0.54  fof(f234,plain,(
% 0.20/0.54    spl6_18 <=> u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.54  fof(f460,plain,(
% 0.20/0.54    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl6_18),
% 0.20/0.54    inference(superposition,[],[f64,f236])).
% 0.20/0.54  fof(f236,plain,(
% 0.20/0.54    u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | ~spl6_18),
% 0.20/0.54    inference(avatar_component_clause,[],[f234])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.20/0.54  fof(f432,plain,(
% 0.20/0.54    spl6_43 | spl6_44 | ~spl6_27),
% 0.20/0.54    inference(avatar_split_clause,[],[f411,f287,f429,f425])).
% 0.20/0.54  fof(f425,plain,(
% 0.20/0.54    spl6_43 <=> v1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.20/0.54  fof(f429,plain,(
% 0.20/0.54    spl6_44 <=> u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.20/0.54  fof(f287,plain,(
% 0.20/0.54    spl6_27 <=> m1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.54  fof(f411,plain,(
% 0.20/0.54    u1_struct_0(sK0) = sK3(sK0,k1_tex_2(sK0,sK1)) | v1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~spl6_27),
% 0.20/0.54    inference(resolution,[],[f289,f73])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.54  fof(f289,plain,(
% 0.20/0.54    m1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_27),
% 0.20/0.54    inference(avatar_component_clause,[],[f287])).
% 0.20/0.54  fof(f327,plain,(
% 0.20/0.54    ~spl6_9 | ~spl6_14),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f325])).
% 0.20/0.54  fof(f325,plain,(
% 0.20/0.54    $false | (~spl6_9 | ~spl6_14)),
% 0.20/0.54    inference(resolution,[],[f137,f212])).
% 0.20/0.54  fof(f212,plain,(
% 0.20/0.54    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl6_14),
% 0.20/0.54    inference(avatar_component_clause,[],[f210])).
% 0.20/0.54  fof(f210,plain,(
% 0.20/0.54    spl6_14 <=> v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_zfmisc_1(X0)) ) | ~spl6_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f136])).
% 0.20/0.54  fof(f136,plain,(
% 0.20/0.54    spl6_9 <=> ! [X0] : ~v1_zfmisc_1(X0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.54  fof(f314,plain,(
% 0.20/0.54    spl6_28 | ~spl6_6 | ~spl6_20),
% 0.20/0.54    inference(avatar_split_clause,[],[f312,f243,f115,f295])).
% 0.20/0.54  fof(f243,plain,(
% 0.20/0.54    spl6_20 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.54  fof(f312,plain,(
% 0.20/0.54    ~l1_struct_0(sK0) | v7_struct_0(sK0) | ~spl6_20),
% 0.20/0.54    inference(resolution,[],[f245,f67])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.20/0.54  fof(f245,plain,(
% 0.20/0.54    v1_zfmisc_1(u1_struct_0(sK0)) | ~spl6_20),
% 0.20/0.54    inference(avatar_component_clause,[],[f243])).
% 0.20/0.54  fof(f311,plain,(
% 0.20/0.54    spl6_20 | spl6_9 | ~spl6_19),
% 0.20/0.54    inference(avatar_split_clause,[],[f307,f239,f136,f243])).
% 0.20/0.54  fof(f239,plain,(
% 0.20/0.54    spl6_19 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.54  fof(f307,plain,(
% 0.20/0.54    ( ! [X3] : (~v1_zfmisc_1(X3) | v1_zfmisc_1(u1_struct_0(sK0))) ) | ~spl6_19),
% 0.20/0.54    inference(resolution,[],[f300,f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_zfmisc_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0] : (v1_zfmisc_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_zfmisc_1(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_1)).
% 0.20/0.54  fof(f300,plain,(
% 0.20/0.54    ( ! [X1] : (m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X1))) ) | ~spl6_19),
% 0.20/0.54    inference(resolution,[],[f291,f82])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.54  fof(f291,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(u1_struct_0(sK0),X0)) ) | ~spl6_19),
% 0.20/0.54    inference(resolution,[],[f241,f139])).
% 0.20/0.54  fof(f139,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f80,f72])).
% 0.20/0.54  % (18871)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f241,plain,(
% 0.20/0.54    v1_xboole_0(u1_struct_0(sK0)) | ~spl6_19),
% 0.20/0.54    inference(avatar_component_clause,[],[f239])).
% 0.20/0.54  fof(f298,plain,(
% 0.20/0.54    spl6_2 | spl6_12 | ~spl6_16 | ~spl6_1 | ~spl6_28 | ~spl6_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f293,f104,f295,f89,f222,f182,f94])).
% 0.20/0.54  fof(f182,plain,(
% 0.20/0.54    spl6_12 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.54  fof(f293,plain,(
% 0.20/0.54    ~v7_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | ~spl6_4),
% 0.20/0.54    inference(resolution,[],[f105,f69])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | ~v7_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v2_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl6_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f104])).
% 0.20/0.54  fof(f290,plain,(
% 0.20/0.54    spl6_4 | spl6_27 | ~spl6_1 | ~spl6_16),
% 0.20/0.54    inference(avatar_split_clause,[],[f285,f222,f89,f287,f104])).
% 0.20/0.54  fof(f285,plain,(
% 0.20/0.54    ~l1_pre_topc(sK0) | m1_subset_1(sK3(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl6_16),
% 0.20/0.54    inference(resolution,[],[f62,f224])).
% 0.20/0.54  fof(f224,plain,(
% 0.20/0.54    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl6_16),
% 0.20/0.54    inference(avatar_component_clause,[],[f222])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f248,plain,(
% 0.20/0.54    spl6_15 | ~spl6_17),
% 0.20/0.54    inference(avatar_split_clause,[],[f247,f228,f214])).
% 0.20/0.54  fof(f214,plain,(
% 0.20/0.54    spl6_15 <=> l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.54  fof(f228,plain,(
% 0.20/0.54    spl6_17 <=> l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.54  fof(f247,plain,(
% 0.20/0.54    l1_struct_0(k1_tex_2(sK0,sK1)) | ~spl6_17),
% 0.20/0.54    inference(resolution,[],[f230,f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.54  fof(f230,plain,(
% 0.20/0.54    l1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl6_17),
% 0.20/0.54    inference(avatar_component_clause,[],[f228])).
% 0.20/0.54  fof(f246,plain,(
% 0.20/0.54    spl6_5 | spl6_19 | spl6_20 | ~spl6_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f174,f99,f243,f239,f108])).
% 0.20/0.54  fof(f174,plain,(
% 0.20/0.54    v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl6_3),
% 0.20/0.54    inference(resolution,[],[f66,f101])).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f99])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0) | v1_subset_1(k6_domain_1(X0,X1),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,axiom,(
% 0.20/0.54    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 0.20/0.54  % (18872)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  fof(f237,plain,(
% 0.20/0.54    spl6_4 | spl6_18 | ~spl6_1 | ~spl6_16),
% 0.20/0.54    inference(avatar_split_clause,[],[f232,f222,f89,f234,f104])).
% 0.20/0.54  fof(f232,plain,(
% 0.20/0.54    ~l1_pre_topc(sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl6_16),
% 0.20/0.54    inference(resolution,[],[f63,f224])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | u1_struct_0(X1) = sK3(X0,X1) | v1_tex_2(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f231,plain,(
% 0.20/0.54    spl6_17 | ~spl6_1 | ~spl6_16),
% 0.20/0.54    inference(avatar_split_clause,[],[f226,f222,f89,f228])).
% 0.20/0.54  fof(f226,plain,(
% 0.20/0.54    ~l1_pre_topc(sK0) | l1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl6_16),
% 0.20/0.54    inference(resolution,[],[f224,f60])).
% 0.20/0.54  % (18875)Refutation not found, incomplete strategy% (18875)------------------------------
% 0.20/0.54  % (18875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (18875)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (18875)Memory used [KB]: 6268
% 0.20/0.54  % (18875)Time elapsed: 0.109 s
% 0.20/0.54  % (18875)------------------------------
% 0.20/0.54  % (18875)------------------------------
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.54  fof(f225,plain,(
% 0.20/0.54    spl6_16 | spl6_2 | ~spl6_1 | ~spl6_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f218,f99,f89,f94,f222])).
% 0.20/0.54  fof(f218,plain,(
% 0.20/0.54    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl6_3),
% 0.20/0.54    inference(resolution,[],[f76,f101])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.54    inference(pure_predicate_removal,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.20/0.54  fof(f217,plain,(
% 0.20/0.54    spl6_14 | ~spl6_15 | ~spl6_13),
% 0.20/0.54    inference(avatar_split_clause,[],[f208,f204,f214,f210])).
% 0.20/0.54  fof(f204,plain,(
% 0.20/0.54    spl6_13 <=> v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.54  fof(f208,plain,(
% 0.20/0.54    ~l1_struct_0(k1_tex_2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl6_13),
% 0.20/0.54    inference(resolution,[],[f206,f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.20/0.54  fof(f206,plain,(
% 0.20/0.54    v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl6_13),
% 0.20/0.54    inference(avatar_component_clause,[],[f204])).
% 0.20/0.54  % (18901)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  fof(f207,plain,(
% 0.20/0.54    spl6_13 | spl6_2 | ~spl6_1 | ~spl6_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f200,f99,f89,f94,f204])).
% 0.20/0.54  fof(f200,plain,(
% 0.20/0.54    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl6_3),
% 0.20/0.54    inference(resolution,[],[f78,f101])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v7_struct_0(k1_tex_2(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.54    inference(pure_predicate_removal,[],[f16])).
% 0.20/0.54  fof(f16,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.20/0.54  fof(f185,plain,(
% 0.20/0.54    ~spl6_12 | spl6_2 | ~spl6_1 | ~spl6_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f180,f99,f89,f94,f182])).
% 0.20/0.54  fof(f180,plain,(
% 0.20/0.54    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl6_3),
% 0.20/0.54    inference(resolution,[],[f75,f101])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    spl6_6 | ~spl6_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f113,f89,f115])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    l1_struct_0(sK0) | ~spl6_1),
% 0.20/0.54    inference(resolution,[],[f59,f91])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    l1_pre_topc(sK0) | ~spl6_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f89])).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    spl6_4 | spl6_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f50,f108,f104])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,negated_conjecture,(
% 0.20/0.54    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.54    inference(negated_conjecture,[],[f20])).
% 0.20/0.54  fof(f20,conjecture,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.20/0.54  fof(f111,plain,(
% 0.20/0.54    ~spl6_4 | ~spl6_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f51,f108,f104])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    spl6_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f52,f99])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    ~spl6_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f53,f94])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ~v2_struct_0(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    spl6_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f54,f89])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    l1_pre_topc(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (18887)------------------------------
% 0.20/0.54  % (18887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (18887)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (18887)Memory used [KB]: 11001
% 0.20/0.54  % (18887)Time elapsed: 0.112 s
% 0.20/0.54  % (18887)------------------------------
% 0.20/0.54  % (18887)------------------------------
% 0.20/0.54  % (18890)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (18872)Refutation not found, incomplete strategy% (18872)------------------------------
% 0.20/0.54  % (18872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (18872)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (18872)Memory used [KB]: 10746
% 0.20/0.54  % (18872)Time elapsed: 0.126 s
% 0.20/0.54  % (18872)------------------------------
% 0.20/0.54  % (18872)------------------------------
% 0.20/0.54  % (18867)Success in time 0.181 s
%------------------------------------------------------------------------------
