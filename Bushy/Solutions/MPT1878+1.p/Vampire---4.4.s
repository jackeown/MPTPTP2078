%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t46_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:52 EDT 2019

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 261 expanded)
%              Number of leaves         :   38 ( 106 expanded)
%              Depth                    :   13
%              Number of atoms          :  503 ( 875 expanded)
%              Number of equality atoms :   53 (  78 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7771,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f131,f138,f145,f152,f173,f208,f228,f235,f239,f264,f392,f837,f1636,f1652,f1658,f2482,f7746,f7756])).

fof(f7756,plain,
    ( ~ spl9_8
    | ~ spl9_480 ),
    inference(avatar_contradiction_clause,[],[f7755])).

fof(f7755,plain,
    ( $false
    | ~ spl9_8
    | ~ spl9_480 ),
    inference(subsumption_resolution,[],[f7747,f151])).

fof(f151,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl9_8
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f7747,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl9_480 ),
    inference(superposition,[],[f85,f7745])).

fof(f7745,plain,
    ( o_0_0_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0)))
    | ~ spl9_480 ),
    inference(avatar_component_clause,[],[f7744])).

fof(f7744,plain,
    ( spl9_480
  <=> o_0_0_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_480])])).

fof(f85,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t46_tex_2.p',fc2_xboole_0)).

fof(f7746,plain,
    ( spl9_480
    | spl9_185
    | ~ spl9_252 ),
    inference(avatar_split_clause,[],[f7739,f2480,f1628,f7744])).

fof(f1628,plain,
    ( spl9_185
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_185])])).

fof(f2480,plain,
    ( spl9_252
  <=> k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_252])])).

fof(f7739,plain,
    ( o_0_0_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0)))
    | ~ spl9_185
    | ~ spl9_252 ),
    inference(forward_demodulation,[],[f1659,f2481])).

fof(f2481,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = o_0_0_xboole_0
    | ~ spl9_252 ),
    inference(avatar_component_clause,[],[f2480])).

fof(f1659,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = k1_tarski(sK3(u1_struct_0(sK0)))
    | ~ spl9_185 ),
    inference(resolution,[],[f1629,f297])).

fof(f297,plain,(
    ! [X3] :
      ( v1_xboole_0(X3)
      | k6_domain_1(X3,sK3(X3)) = k1_tarski(sK3(X3)) ) ),
    inference(duplicate_literal_removal,[],[f295])).

fof(f295,plain,(
    ! [X3] :
      ( k6_domain_1(X3,sK3(X3)) = k1_tarski(sK3(X3))
      | v1_xboole_0(X3)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f106,f272])).

fof(f272,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f104,f99])).

fof(f99,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f66,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t46_tex_2.p',d1_xboole_0)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t46_tex_2.p',t1_subset)).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t46_tex_2.p',redefinition_k6_domain_1)).

fof(f1629,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_185 ),
    inference(avatar_component_clause,[],[f1628])).

fof(f2482,plain,
    ( spl9_252
    | spl9_185
    | ~ spl9_186 ),
    inference(avatar_split_clause,[],[f1668,f1634,f1628,f2480])).

fof(f1634,plain,
    ( spl9_186
  <=> ! [X0] :
        ( k6_domain_1(u1_struct_0(sK0),X0) = o_0_0_xboole_0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_186])])).

fof(f1668,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = o_0_0_xboole_0
    | ~ spl9_185
    | ~ spl9_186 ),
    inference(subsumption_resolution,[],[f1663,f1629])).

fof(f1663,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = o_0_0_xboole_0
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_186 ),
    inference(resolution,[],[f1635,f272])).

fof(f1635,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k6_domain_1(u1_struct_0(sK0),X0) = o_0_0_xboole_0 )
    | ~ spl9_186 ),
    inference(avatar_component_clause,[],[f1634])).

fof(f1658,plain,
    ( ~ spl9_4
    | spl9_189 ),
    inference(avatar_contradiction_clause,[],[f1657])).

fof(f1657,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_189 ),
    inference(subsumption_resolution,[],[f1655,f137])).

fof(f137,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl9_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f1655,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl9_189 ),
    inference(resolution,[],[f1651,f87])).

fof(f87,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t46_tex_2.p',dt_l1_pre_topc)).

fof(f1651,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl9_189 ),
    inference(avatar_component_clause,[],[f1650])).

fof(f1650,plain,
    ( spl9_189
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_189])])).

fof(f1652,plain,
    ( ~ spl9_189
    | spl9_1
    | ~ spl9_184 ),
    inference(avatar_split_clause,[],[f1643,f1631,f122,f1650])).

fof(f122,plain,
    ( spl9_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f1631,plain,
    ( spl9_184
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_184])])).

fof(f1643,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl9_1
    | ~ spl9_184 ),
    inference(subsumption_resolution,[],[f1637,f123])).

fof(f123,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1637,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_184 ),
    inference(resolution,[],[f1632,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t46_tex_2.p',fc2_struct_0)).

fof(f1632,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_184 ),
    inference(avatar_component_clause,[],[f1631])).

fof(f1636,plain,
    ( spl9_184
    | spl9_186
    | ~ spl9_108 ),
    inference(avatar_split_clause,[],[f852,f835,f1634,f1631])).

fof(f835,plain,
    ( spl9_108
  <=> ! [X0] :
        ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),X0) = o_0_0_xboole_0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_108])])).

fof(f852,plain,
    ( ! [X0] :
        ( k6_domain_1(u1_struct_0(sK0),X0) = o_0_0_xboole_0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl9_108 ),
    inference(duplicate_literal_removal,[],[f849])).

fof(f849,plain,
    ( ! [X0] :
        ( k6_domain_1(u1_struct_0(sK0),X0) = o_0_0_xboole_0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl9_108 ),
    inference(resolution,[],[f836,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t46_tex_2.p',dt_k6_domain_1)).

fof(f836,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),X0) = o_0_0_xboole_0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_108 ),
    inference(avatar_component_clause,[],[f835])).

fof(f837,plain,
    ( spl9_108
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f400,f390,f136,f129,f122,f835])).

fof(f129,plain,
    ( spl9_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f390,plain,
    ( spl9_62
  <=> ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | o_0_0_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f400,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),X0) = o_0_0_xboole_0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_62 ),
    inference(subsumption_resolution,[],[f399,f123])).

fof(f399,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),X0) = o_0_0_xboole_0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_62 ),
    inference(subsumption_resolution,[],[f398,f130])).

fof(f130,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f129])).

fof(f398,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),X0) = o_0_0_xboole_0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_62 ),
    inference(subsumption_resolution,[],[f395,f137])).

fof(f395,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),X0) = o_0_0_xboole_0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_62 ),
    inference(resolution,[],[f391,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t46_tex_2.p',t36_tex_2)).

fof(f391,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | o_0_0_xboole_0 = X0 )
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f390])).

fof(f392,plain,
    ( spl9_62
    | ~ spl9_4
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f338,f262,f237,f233,f136,f390])).

fof(f233,plain,
    ( spl9_28
  <=> v3_tex_2(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f237,plain,
    ( spl9_30
  <=> ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f262,plain,
    ( spl9_38
  <=> ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f338,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | o_0_0_xboole_0 = X0 )
    | ~ spl9_4
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f337,f137])).

fof(f337,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | o_0_0_xboole_0 = X0
        | ~ l1_pre_topc(sK0) )
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f336,f263])).

fof(f263,plain,
    ( ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f262])).

fof(f336,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | o_0_0_xboole_0 = X0
        | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f335,f238])).

fof(f238,plain,
    ( ! [X0] : r1_tarski(o_0_0_xboole_0,X0)
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f237])).

fof(f335,plain,
    ( ! [X0] :
        ( ~ r1_tarski(o_0_0_xboole_0,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | o_0_0_xboole_0 = X0
        | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl9_28 ),
    inference(resolution,[],[f89,f234])).

fof(f234,plain,
    ( v3_tex_2(o_0_0_xboole_0,sK0)
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f233])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t46_tex_2.p',d7_tex_2)).

fof(f264,plain,
    ( spl9_38
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f255,f226,f262])).

fof(f226,plain,
    ( spl9_26
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f255,plain,
    ( ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))
    | ~ spl9_26 ),
    inference(backward_demodulation,[],[f254,f101])).

fof(f101,plain,(
    ! [X0] : m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( v1_xboole_0(sK5(X0))
      & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK5(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t46_tex_2.p',rc2_subset_1)).

fof(f254,plain,
    ( ! [X0] : o_0_0_xboole_0 = sK5(X0)
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f183,f227])).

fof(f227,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f226])).

fof(f183,plain,(
    ! [X0] : k1_xboole_0 = sK5(X0) ),
    inference(resolution,[],[f95,f102])).

fof(f102,plain,(
    ! [X0] : v1_xboole_0(sK5(X0)) ),
    inference(cnf_transformation,[],[f72])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t46_tex_2.p',t6_boole)).

fof(f239,plain,
    ( spl9_30
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f221,f150,f237])).

fof(f221,plain,
    ( ! [X0] : r1_tarski(o_0_0_xboole_0,X0)
    | ~ spl9_8 ),
    inference(backward_demodulation,[],[f182,f86])).

fof(f86,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t46_tex_2.p',t2_xboole_1)).

fof(f182,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl9_8 ),
    inference(resolution,[],[f95,f151])).

fof(f235,plain,
    ( spl9_28
    | ~ spl9_8
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f218,f206,f150,f233])).

fof(f206,plain,
    ( spl9_22
  <=> v3_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f218,plain,
    ( v3_tex_2(o_0_0_xboole_0,sK0)
    | ~ spl9_8
    | ~ spl9_22 ),
    inference(backward_demodulation,[],[f182,f207])).

fof(f207,plain,
    ( v3_tex_2(k1_xboole_0,sK0)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f206])).

fof(f228,plain,
    ( spl9_26
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f182,f150,f226])).

fof(f208,plain,
    ( spl9_22
    | ~ spl9_6
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f185,f171,f143,f206])).

fof(f143,plain,
    ( spl9_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f171,plain,
    ( spl9_14
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f185,plain,
    ( v3_tex_2(k1_xboole_0,sK0)
    | ~ spl9_6
    | ~ spl9_14 ),
    inference(backward_demodulation,[],[f181,f172])).

fof(f172,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f171])).

fof(f181,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_6 ),
    inference(resolution,[],[f95,f144])).

fof(f144,plain,
    ( v1_xboole_0(sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f143])).

fof(f173,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f83,f171])).

fof(f83,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( v3_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f58,f57])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v3_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( v3_tex_2(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
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
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t46_tex_2.p',t46_tex_2)).

fof(f152,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f84,f150])).

fof(f84,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t46_tex_2.p',dt_o_0_0_xboole_0)).

fof(f145,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f81,f143])).

fof(f81,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f138,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f80,f136])).

fof(f80,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f131,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f79,f129])).

fof(f79,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f124,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f78,f122])).

fof(f78,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
