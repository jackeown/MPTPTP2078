%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1371+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:49 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 491 expanded)
%              Number of leaves         :   44 ( 213 expanded)
%              Depth                    :   22
%              Number of atoms          : 1165 (3901 expanded)
%              Number of equality atoms :  104 ( 487 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f715,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f162,f167,f172,f177,f215,f272,f358,f409,f432,f519,f713,f714])).

fof(f714,plain,
    ( sK4(sK0,sK1,sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2)))
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f713,plain,
    ( spl5_44
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_18
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f548,f355,f212,f169,f164,f159,f137,f122,f710])).

fof(f710,plain,
    ( spl5_44
  <=> sK4(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f122,plain,
    ( spl5_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f137,plain,
    ( spl5_9
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f159,plain,
    ( spl5_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f164,plain,
    ( spl5_14
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f169,plain,
    ( spl5_15
  <=> k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f212,plain,
    ( spl5_18
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f355,plain,
    ( spl5_27
  <=> r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

% (20489)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f548,plain,
    ( sK4(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2)))
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_18
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f357,f376])).

fof(f376,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f375,f222])).

fof(f222,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f139,f124,f214,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f214,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f212])).

fof(f124,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f139,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f137])).

fof(f375,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_18 ),
    inference(resolution,[],[f229,f86])).

% (20495)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f229,plain,
    ( ! [X1] :
        ( r1_tarski(X1,k10_relat_1(sK2,k9_relat_1(sK2,X1)))
        | ~ r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f228,f207])).

fof(f207,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f166,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f166,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f228,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k2_struct_0(sK0))
        | r1_tarski(X1,k10_relat_1(sK2,k9_relat_1(sK2,X1))) )
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f225,f196])).

fof(f196,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f193,f171])).

fof(f171,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f169])).

fof(f193,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f161,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f161,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f225,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK2))
        | r1_tarski(X1,k10_relat_1(sK2,k9_relat_1(sK2,X1))) )
    | ~ spl5_18 ),
    inference(resolution,[],[f214,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f357,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f355])).

fof(f519,plain,
    ( spl5_36
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f449,f406,f159,f152,f142,f122,f117,f102,f516])).

fof(f516,plain,
    ( spl5_36
  <=> v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f102,plain,
    ( spl5_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f117,plain,
    ( spl5_5
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f142,plain,
    ( spl5_10
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f152,plain,
    ( spl5_12
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f406,plain,
    ( spl5_32
  <=> v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f449,plain,
    ( v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),sK0)
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f445,f201])).

fof(f201,plain,
    ( ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f161,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f445,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),sK0)
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f104,f119,f124,f144,f154,f161,f289,f408,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v4_pre_topc(X4,X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
                    & v4_pre_topc(sK3(X0,X1,X2),X1)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
        & v4_pre_topc(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f408,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f406])).

fof(f289,plain,
    ( ! [X0] : m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_13 ),
    inference(superposition,[],[f198,f204])).

fof(f204,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f161,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f198,plain,
    ( ! [X0] : m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f161,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f154,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f152])).

fof(f144,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f119,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f104,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f432,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_31 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f430,f416])).

fof(f416,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_31 ),
    inference(forward_demodulation,[],[f411,f204])).

fof(f411,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f99,f104,f109,f114,f119,f124,f134,f129,f144,f154,f161,f176,f271,f404,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X3,X0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v8_pre_topc(X1)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v5_pre_topc(X2,X0,X1)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ v8_pre_topc(X1)
              | ~ v1_compts_1(X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v5_pre_topc(X2,X0,X1)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ v8_pre_topc(X1)
              | ~ v1_compts_1(X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v5_pre_topc(X2,X0,X1)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( v4_pre_topc(X3,X0)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_compts_1)).

fof(f404,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl5_31
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f271,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl5_24
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f176,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl5_16
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f129,plain,
    ( v1_compts_1(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_7
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f134,plain,
    ( v8_pre_topc(sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl5_8
  <=> v8_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f114,plain,
    ( v2_pre_topc(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f109,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f99,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f430,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl5_2
    | spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_31 ),
    inference(forward_demodulation,[],[f429,f204])).

fof(f429,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl5_2
    | spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f428,f104])).

fof(f428,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ l1_pre_topc(sK0)
    | spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f427,f109])).

fof(f427,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f426,f119])).

fof(f426,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f425,f124])).

fof(f425,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f424,f154])).

fof(f424,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_9
    | spl5_11
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f423,f161])).

fof(f423,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_9
    | spl5_11
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f422,f171])).

fof(f422,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_9
    | spl5_11
    | ~ spl5_16
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f421,f176])).

fof(f421,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_9
    | spl5_11
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f420,f139])).

fof(f420,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | spl5_11
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f412,f149])).

fof(f149,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl5_11
  <=> v3_tops_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f412,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_31 ),
    inference(resolution,[],[f404,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
      | v3_tops_2(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
                      | ~ v4_pre_topc(sK4(X0,X1,X2),X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
                      | v4_pre_topc(sK4(X0,X1,X2),X0) )
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( ! [X4] :
                        ( ( ( v4_pre_topc(X4,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                            | ~ v4_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
            | ~ v4_pre_topc(X3,X0) )
          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
            | v4_pre_topc(X3,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
          | ~ v4_pre_topc(sK4(X0,X1,X2),X0) )
        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
          | v4_pre_topc(sK4(X0,X1,X2),X0) )
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( ! [X4] :
                        ( ( ( v4_pre_topc(X4,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                            | ~ v4_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f45])).

% (20498)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( ! [X3] :
                        ( ( ( v4_pre_topc(X3,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                            | ~ v4_pre_topc(X3,X0) ) )
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( ! [X3] :
                        ( ( ( v4_pre_topc(X3,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                            | ~ v4_pre_topc(X3,X0) ) )
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_2)).

fof(f409,plain,
    ( spl5_31
    | spl5_32
    | ~ spl5_2
    | spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f330,f174,f169,f159,f152,f147,f137,f122,f117,f107,f102,f406,f402])).

fof(f330,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl5_2
    | spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f329,f204])).

fof(f329,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl5_2
    | spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f328,f104])).

fof(f328,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ l1_pre_topc(sK0)
    | spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f327,f109])).

fof(f327,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f326,f119])).

fof(f326,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f325,f161])).

fof(f325,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f324,f171])).

fof(f324,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f323,f176])).

fof(f323,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f322,f149])).

fof(f322,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(resolution,[],[f219,f154])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | v4_pre_topc(sK4(X0,X1,sK2),X0)
        | v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK4(X0,X1,sK2)),X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f218,f124])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK4(X0,X1,sK2)),X1)
        | v4_pre_topc(sK4(X0,X1,sK2),X0)
        | v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f79,f139])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
      | v4_pre_topc(sK4(X0,X1,X2),X0)
      | v3_tops_2(X2,X0,X1)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f358,plain,
    ( spl5_27
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f273,f269,f355])).

fof(f273,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f271,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f272,plain,
    ( spl5_24
    | ~ spl5_2
    | spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f216,f174,f169,f159,f152,f147,f137,f122,f117,f107,f102,f269])).

fof(f216,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2
    | spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f104,f109,f119,f124,f139,f149,f154,f161,f171,f176,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tops_2(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f215,plain,
    ( spl5_18
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f183,f159,f212])).

fof(f183,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f161,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f177,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f63,f174])).

fof(f63,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    & v5_pre_topc(sK2,sK0,sK1)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & v8_pre_topc(sK1)
    & v1_compts_1(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_tops_2(X2,X0,X1)
                & v5_pre_topc(X2,X0,X1)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                & v8_pre_topc(X1)
                & v1_compts_1(X0)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,sK0,X1)
              & v5_pre_topc(X2,sK0,X1)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & v8_pre_topc(X1)
              & v1_compts_1(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v3_tops_2(X2,sK0,X1)
            & v5_pre_topc(X2,sK0,X1)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & v8_pre_topc(X1)
            & v1_compts_1(sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ v3_tops_2(X2,sK0,sK1)
          & v5_pre_topc(X2,sK0,sK1)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          & v8_pre_topc(sK1)
          & v1_compts_1(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ~ v3_tops_2(X2,sK0,sK1)
        & v5_pre_topc(X2,sK0,sK1)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
        & v8_pre_topc(sK1)
        & v1_compts_1(sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ v3_tops_2(sK2,sK0,sK1)
      & v5_pre_topc(sK2,sK0,sK1)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & v8_pre_topc(sK1)
      & v1_compts_1(sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & v8_pre_topc(X1)
                    & v1_compts_1(X0) )
                 => v3_tops_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => v3_tops_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_compts_1)).

fof(f172,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f62,f169])).

fof(f62,plain,(
    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f167,plain,
    ( spl5_14
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f156,f102,f164])).

fof(f156,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f104,f68])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f162,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f59,f159])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f155,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f58,f152])).

fof(f58,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f150,plain,(
    ~ spl5_11 ),
    inference(avatar_split_clause,[],[f66,f147])).

fof(f66,plain,(
    ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f145,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f65,f142])).

fof(f65,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f140,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f64,f137])).

fof(f64,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f135,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f61,f132])).

fof(f61,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f130,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f60,f127])).

fof(f60,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f125,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f57,f122])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f120,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f56,f117])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f115,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f55,f112])).

fof(f55,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f110,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f54,f107])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f105,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f53,f102])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f52,f97])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

%------------------------------------------------------------------------------
