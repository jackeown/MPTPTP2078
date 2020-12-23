%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1869+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:48 EST 2020

% Result     : Theorem 2.83s
% Output     : Refutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  309 ( 715 expanded)
%              Number of leaves         :   51 ( 269 expanded)
%              Depth                    :   17
%              Number of atoms          : 1296 (2541 expanded)
%              Number of equality atoms :   80 ( 240 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f134,f139,f146,f178,f185,f385,f489,f504,f536,f554,f764,f1050,f1095,f1103,f1126,f1147,f1162,f1172,f4120,f4154,f6121,f6135,f6151,f6156,f6189,f6190,f6200])).

fof(f6200,plain,
    ( spl9_1
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_9
    | spl9_24
    | spl9_92 ),
    inference(avatar_contradiction_clause,[],[f6199])).

fof(f6199,plain,
    ( $false
    | spl9_1
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_9
    | spl9_24
    | spl9_92 ),
    inference(subsumption_resolution,[],[f6198,f184])).

fof(f184,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl9_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f6198,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_7
    | spl9_24
    | spl9_92 ),
    inference(subsumption_resolution,[],[f6197,f429])).

fof(f429,plain,
    ( ~ v1_xboole_0(sK1)
    | spl9_24 ),
    inference(avatar_component_clause,[],[f427])).

fof(f427,plain,
    ( spl9_24
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f6197,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_7
    | spl9_92 ),
    inference(resolution,[],[f3821,f223])).

fof(f223,plain,
    ( ! [X1] :
        ( m1_pre_topc(sK6(sK0,X1),sK0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl9_1
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f222,f145])).

fof(f145,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl9_7
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f222,plain,
    ( ! [X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_pre_topc(sK6(sK0,X1),sK0) )
    | spl9_1
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f119,f111])).

fof(f111,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl9_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f119,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_pre_topc(sK6(sK0,X1),sK0) )
    | spl9_1 ),
    inference(resolution,[],[f101,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f101,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl9_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f3821,plain,
    ( ~ m1_pre_topc(sK6(sK0,sK1),sK0)
    | spl9_92 ),
    inference(avatar_component_clause,[],[f3820])).

fof(f3820,plain,
    ( spl9_92
  <=> m1_pre_topc(sK6(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).

fof(f6190,plain,
    ( sK7(sK6(sK0,sK1)) != k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1))))
    | v3_pre_topc(sK7(sK6(sK0,sK1)),sK6(sK0,sK1))
    | ~ v3_pre_topc(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),sK6(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f6189,plain,
    ( spl9_150
    | spl9_8
    | ~ spl9_47
    | ~ spl9_48
    | ~ spl9_146 ),
    inference(avatar_split_clause,[],[f6161,f6148,f1169,f1159,f175,f6186])).

fof(f6186,plain,
    ( spl9_150
  <=> sK7(sK6(sK0,sK1)) = k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_150])])).

fof(f175,plain,
    ( spl9_8
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f1159,plain,
    ( spl9_47
  <=> m1_subset_1(sK8(sK6(sK0,sK1)),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f1169,plain,
    ( spl9_48
  <=> sK7(sK6(sK0,sK1)) = k1_tarski(sK8(sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f6148,plain,
    ( spl9_146
  <=> k6_domain_1(k2_struct_0(sK0),sK8(sK6(sK0,sK1))) = k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_146])])).

fof(f6161,plain,
    ( sK7(sK6(sK0,sK1)) = k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1))))
    | spl9_8
    | ~ spl9_47
    | ~ spl9_48
    | ~ spl9_146 ),
    inference(forward_demodulation,[],[f6160,f1171])).

fof(f1171,plain,
    ( sK7(sK6(sK0,sK1)) = k1_tarski(sK8(sK6(sK0,sK1)))
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f1169])).

fof(f6160,plain,
    ( k1_tarski(sK8(sK6(sK0,sK1))) = k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1))))
    | spl9_8
    | ~ spl9_47
    | ~ spl9_146 ),
    inference(subsumption_resolution,[],[f6159,f177])).

fof(f177,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl9_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f6159,plain,
    ( k1_tarski(sK8(sK6(sK0,sK1))) = k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1))))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ spl9_47
    | ~ spl9_146 ),
    inference(subsumption_resolution,[],[f6157,f1161])).

fof(f1161,plain,
    ( m1_subset_1(sK8(sK6(sK0,sK1)),k2_struct_0(sK0))
    | ~ spl9_47 ),
    inference(avatar_component_clause,[],[f1159])).

fof(f6157,plain,
    ( k1_tarski(sK8(sK6(sK0,sK1))) = k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1))))
    | ~ m1_subset_1(sK8(sK6(sK0,sK1)),k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ spl9_146 ),
    inference(superposition,[],[f6150,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f6150,plain,
    ( k6_domain_1(k2_struct_0(sK0),sK8(sK6(sK0,sK1))) = k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1))))
    | ~ spl9_146 ),
    inference(avatar_component_clause,[],[f6148])).

fof(f6156,plain,
    ( spl9_147
    | ~ spl9_21
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_145 ),
    inference(avatar_split_clause,[],[f6144,f6132,f551,f471,f382,f6153])).

fof(f6153,plain,
    ( spl9_147
  <=> v3_pre_topc(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_147])])).

fof(f382,plain,
    ( spl9_21
  <=> sK1 = u1_struct_0(sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f471,plain,
    ( spl9_25
  <=> l1_pre_topc(sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f551,plain,
    ( spl9_27
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f6132,plain,
    ( spl9_145
  <=> r2_hidden(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),u1_pre_topc(sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_145])])).

fof(f6144,plain,
    ( v3_pre_topc(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),sK6(sK0,sK1))
    | ~ spl9_21
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_145 ),
    inference(subsumption_resolution,[],[f6138,f626])).

fof(f626,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(sK1))
    | ~ spl9_27 ),
    inference(superposition,[],[f612,f88])).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f612,plain,
    ( ! [X1] : m1_subset_1(k3_xboole_0(X1,sK1),k1_zfmisc_1(sK1))
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f611,f553])).

fof(f553,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f551])).

fof(f611,plain,
    ( ! [X1] :
        ( m1_subset_1(k3_xboole_0(X1,sK1),k1_zfmisc_1(sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) )
    | ~ spl9_27 ),
    inference(superposition,[],[f592,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f592,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(sK1,X0,sK1),k1_zfmisc_1(sK1))
    | ~ spl9_27 ),
    inference(superposition,[],[f576,f555])).

fof(f555,plain,
    ( ! [X0] : k9_subset_1(sK1,X0,sK1) = k9_subset_1(sK1,sK1,X0)
    | ~ spl9_27 ),
    inference(resolution,[],[f553,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f576,plain,
    ( ! [X1] : m1_subset_1(k9_subset_1(sK1,sK1,X1),k1_zfmisc_1(sK1))
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f571,f553])).

fof(f571,plain,
    ( ! [X1] :
        ( m1_subset_1(k9_subset_1(sK1,sK1,X1),k1_zfmisc_1(sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) )
    | ~ spl9_27 ),
    inference(superposition,[],[f91,f555])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f6138,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),k1_zfmisc_1(sK1))
    | v3_pre_topc(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),sK6(sK0,sK1))
    | ~ spl9_21
    | ~ spl9_25
    | ~ spl9_145 ),
    inference(resolution,[],[f6134,f505])).

fof(f505,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,u1_pre_topc(sK6(sK0,sK1)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
        | v3_pre_topc(X6,sK6(sK0,sK1)) )
    | ~ spl9_21
    | ~ spl9_25 ),
    inference(forward_demodulation,[],[f500,f384])).

fof(f384,plain,
    ( sK1 = u1_struct_0(sK6(sK0,sK1))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f382])).

fof(f500,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK6(sK0,sK1))))
        | ~ r2_hidden(X6,u1_pre_topc(sK6(sK0,sK1)))
        | v3_pre_topc(X6,sK6(sK0,sK1)) )
    | ~ spl9_25 ),
    inference(resolution,[],[f473,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f473,plain,
    ( l1_pre_topc(sK6(sK0,sK1))
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f471])).

fof(f6134,plain,
    ( r2_hidden(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),u1_pre_topc(sK6(sK0,sK1)))
    | ~ spl9_145 ),
    inference(avatar_component_clause,[],[f6132])).

fof(f6151,plain,
    ( spl9_146
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_44
    | ~ spl9_47 ),
    inference(avatar_split_clause,[],[f6136,f1159,f1123,f182,f143,f136,f6148])).

fof(f136,plain,
    ( spl9_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f1123,plain,
    ( spl9_44
  <=> r2_hidden(sK8(sK6(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f6136,plain,
    ( k6_domain_1(k2_struct_0(sK0),sK8(sK6(sK0,sK1))) = k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1))))
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_44
    | ~ spl9_47 ),
    inference(subsumption_resolution,[],[f1132,f1161])).

fof(f1132,plain,
    ( k6_domain_1(k2_struct_0(sK0),sK8(sK6(sK0,sK1))) = k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1))))
    | ~ m1_subset_1(sK8(sK6(sK0,sK1)),k2_struct_0(sK0))
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f1131,f88])).

fof(f1131,plain,
    ( k6_domain_1(k2_struct_0(sK0),sK8(sK6(sK0,sK1))) = k3_xboole_0(sK2(sK8(sK6(sK0,sK1))),sK1)
    | ~ m1_subset_1(sK8(sK6(sK0,sK1)),k2_struct_0(sK0))
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f1128,f195])).

fof(f195,plain,
    ( ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,X1)
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f189,f184])).

fof(f189,plain,
    ( ! [X1] :
        ( k3_xboole_0(X1,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(superposition,[],[f180,f92])).

fof(f180,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,X0)
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f141,f145])).

fof(f141,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl9_6 ),
    inference(resolution,[],[f138,f93])).

fof(f138,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f1128,plain,
    ( ~ m1_subset_1(sK8(sK6(sK0,sK1)),k2_struct_0(sK0))
    | k9_subset_1(k2_struct_0(sK0),sK1,sK2(sK8(sK6(sK0,sK1)))) = k6_domain_1(k2_struct_0(sK0),sK8(sK6(sK0,sK1)))
    | ~ spl9_7
    | ~ spl9_44 ),
    inference(resolution,[],[f1125,f173])).

fof(f173,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,k2_struct_0(sK0))
        | k9_subset_1(k2_struct_0(sK0),sK1,sK2(X2)) = k6_domain_1(k2_struct_0(sK0),X2) )
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f172,f145])).

fof(f172,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k2_struct_0(sK0))
        | ~ r2_hidden(X2,sK1)
        | k9_subset_1(u1_struct_0(sK0),sK1,sK2(X2)) = k6_domain_1(u1_struct_0(sK0),X2) )
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f53,f145])).

fof(f53,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK2(X2)) = k6_domain_1(u1_struct_0(sK0),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                              & v3_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) )
             => v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tex_2)).

fof(f1125,plain,
    ( r2_hidden(sK8(sK6(sK0,sK1)),sK1)
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f1123])).

fof(f6135,plain,
    ( spl9_145
    | ~ spl9_3
    | ~ spl9_21
    | ~ spl9_27
    | ~ spl9_92
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f6128,f6118,f3820,f551,f382,f109,f6132])).

fof(f6118,plain,
    ( spl9_144
  <=> sP4(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),sK6(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_144])])).

fof(f6128,plain,
    ( r2_hidden(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),u1_pre_topc(sK6(sK0,sK1)))
    | ~ spl9_3
    | ~ spl9_21
    | ~ spl9_27
    | ~ spl9_92
    | ~ spl9_144 ),
    inference(subsumption_resolution,[],[f6127,f626])).

fof(f6127,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),k1_zfmisc_1(sK1))
    | r2_hidden(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),u1_pre_topc(sK6(sK0,sK1)))
    | ~ spl9_3
    | ~ spl9_21
    | ~ spl9_92
    | ~ spl9_144 ),
    inference(forward_demodulation,[],[f6126,f384])).

fof(f6126,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),k1_zfmisc_1(u1_struct_0(sK6(sK0,sK1))))
    | r2_hidden(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),u1_pre_topc(sK6(sK0,sK1)))
    | ~ spl9_3
    | ~ spl9_92
    | ~ spl9_144 ),
    inference(subsumption_resolution,[],[f6123,f3822])).

fof(f3822,plain,
    ( m1_pre_topc(sK6(sK0,sK1),sK0)
    | ~ spl9_92 ),
    inference(avatar_component_clause,[],[f3820])).

fof(f6123,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),k1_zfmisc_1(u1_struct_0(sK6(sK0,sK1))))
    | r2_hidden(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),u1_pre_topc(sK6(sK0,sK1)))
    | ~ m1_pre_topc(sK6(sK0,sK1),sK0)
    | ~ spl9_3
    | ~ spl9_144 ),
    inference(resolution,[],[f6120,f245])).

fof(f245,plain,
    ( ! [X0,X1] :
        ( ~ sP4(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(X1,u1_pre_topc(X0))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f122,f125])).

fof(f125,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK0)
        | l1_pre_topc(X5) )
    | ~ spl9_3 ),
    inference(resolution,[],[f111,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ sP4(X1,X0,sK0)
        | r2_hidden(X1,u1_pre_topc(X0))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl9_3 ),
    inference(resolution,[],[f111,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP4(X2,X1,X0)
      | r2_hidden(X2,u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f6120,plain,
    ( sP4(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),sK6(sK0,sK1),sK0)
    | ~ spl9_144 ),
    inference(avatar_component_clause,[],[f6118])).

fof(f6121,plain,
    ( spl9_144
    | ~ spl9_7
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_27
    | ~ spl9_106
    | ~ spl9_108 ),
    inference(avatar_split_clause,[],[f4231,f4151,f4117,f551,f533,f382,f143,f6118])).

fof(f533,plain,
    ( spl9_26
  <=> sK1 = k2_struct_0(sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f4117,plain,
    ( spl9_106
  <=> m1_subset_1(sK2(sK8(sK6(sK0,sK1))),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f4151,plain,
    ( spl9_108
  <=> r2_hidden(sK2(sK8(sK6(sK0,sK1))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_108])])).

fof(f4231,plain,
    ( sP4(k3_xboole_0(sK1,sK2(sK8(sK6(sK0,sK1)))),sK6(sK0,sK1),sK0)
    | ~ spl9_7
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_27
    | ~ spl9_106
    | ~ spl9_108 ),
    inference(forward_demodulation,[],[f4230,f88])).

fof(f4230,plain,
    ( sP4(k3_xboole_0(sK2(sK8(sK6(sK0,sK1))),sK1),sK6(sK0,sK1),sK0)
    | ~ spl9_7
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_27
    | ~ spl9_106
    | ~ spl9_108 ),
    inference(forward_demodulation,[],[f4229,f574])).

fof(f574,plain,
    ( ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(sK1,sK1,X1)
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f568,f553])).

fof(f568,plain,
    ( ! [X1] :
        ( k3_xboole_0(X1,sK1) = k9_subset_1(sK1,sK1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) )
    | ~ spl9_27 ),
    inference(superposition,[],[f555,f92])).

fof(f4229,plain,
    ( sP4(k9_subset_1(sK1,sK1,sK2(sK8(sK6(sK0,sK1)))),sK6(sK0,sK1),sK0)
    | ~ spl9_7
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_27
    | ~ spl9_106
    | ~ spl9_108 ),
    inference(forward_demodulation,[],[f4228,f555])).

fof(f4228,plain,
    ( sP4(k9_subset_1(sK1,sK2(sK8(sK6(sK0,sK1))),sK1),sK6(sK0,sK1),sK0)
    | ~ spl9_7
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_106
    | ~ spl9_108 ),
    inference(forward_demodulation,[],[f4210,f535])).

fof(f535,plain,
    ( sK1 = k2_struct_0(sK6(sK0,sK1))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f533])).

fof(f4210,plain,
    ( sP4(k9_subset_1(sK1,sK2(sK8(sK6(sK0,sK1))),k2_struct_0(sK6(sK0,sK1))),sK6(sK0,sK1),sK0)
    | ~ spl9_7
    | ~ spl9_21
    | ~ spl9_106
    | ~ spl9_108 ),
    inference(superposition,[],[f4162,f384])).

fof(f4162,plain,
    ( ! [X0] : sP4(k9_subset_1(u1_struct_0(X0),sK2(sK8(sK6(sK0,sK1))),k2_struct_0(X0)),X0,sK0)
    | ~ spl9_7
    | ~ spl9_106
    | ~ spl9_108 ),
    inference(subsumption_resolution,[],[f4161,f4119])).

fof(f4119,plain,
    ( m1_subset_1(sK2(sK8(sK6(sK0,sK1))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl9_106 ),
    inference(avatar_component_clause,[],[f4117])).

fof(f4161,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK8(sK6(sK0,sK1))),k1_zfmisc_1(k2_struct_0(sK0)))
        | sP4(k9_subset_1(u1_struct_0(X0),sK2(sK8(sK6(sK0,sK1))),k2_struct_0(X0)),X0,sK0) )
    | ~ spl9_7
    | ~ spl9_108 ),
    inference(forward_demodulation,[],[f4158,f145])).

fof(f4158,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK8(sK6(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | sP4(k9_subset_1(u1_struct_0(X0),sK2(sK8(sK6(sK0,sK1))),k2_struct_0(X0)),X0,sK0) )
    | ~ spl9_108 ),
    inference(resolution,[],[f4153,f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,u1_pre_topc(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | sP4(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | sP4(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4153,plain,
    ( r2_hidden(sK2(sK8(sK6(sK0,sK1))),u1_pre_topc(sK0))
    | ~ spl9_108 ),
    inference(avatar_component_clause,[],[f4151])).

fof(f4154,plain,
    ( spl9_108
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_44
    | ~ spl9_47
    | ~ spl9_106 ),
    inference(avatar_split_clause,[],[f4131,f4117,f1159,f1123,f143,f109,f4151])).

fof(f4131,plain,
    ( r2_hidden(sK2(sK8(sK6(sK0,sK1))),u1_pre_topc(sK0))
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_44
    | ~ spl9_47
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f4130,f1125])).

fof(f4130,plain,
    ( r2_hidden(sK2(sK8(sK6(sK0,sK1))),u1_pre_topc(sK0))
    | ~ r2_hidden(sK8(sK6(sK0,sK1)),sK1)
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_47
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f4122,f1161])).

fof(f4122,plain,
    ( r2_hidden(sK2(sK8(sK6(sK0,sK1))),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK8(sK6(sK0,sK1)),k2_struct_0(sK0))
    | ~ r2_hidden(sK8(sK6(sK0,sK1)),sK1)
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_106 ),
    inference(resolution,[],[f4119,f209])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(sK2(X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f206,f145])).

fof(f206,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK2(X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(resolution,[],[f188,f52])).

fof(f52,plain,(
    ! [X2] :
      ( v3_pre_topc(sK2(X2),sK0)
      | ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f188,plain,
    ( ! [X7] :
        ( ~ v3_pre_topc(X7,sK0)
        | r2_hidden(X7,u1_pre_topc(sK0))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f127,f145])).

fof(f127,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X7,u1_pre_topc(sK0))
        | ~ v3_pre_topc(X7,sK0) )
    | ~ spl9_3 ),
    inference(resolution,[],[f111,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4120,plain,
    ( spl9_106
    | ~ spl9_7
    | ~ spl9_44
    | ~ spl9_47 ),
    inference(avatar_split_clause,[],[f4051,f1159,f1123,f143,f4117])).

fof(f4051,plain,
    ( m1_subset_1(sK2(sK8(sK6(sK0,sK1))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl9_7
    | ~ spl9_44
    | ~ spl9_47 ),
    inference(subsumption_resolution,[],[f1134,f1161])).

fof(f1134,plain,
    ( m1_subset_1(sK2(sK8(sK6(sK0,sK1))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK8(sK6(sK0,sK1)),k2_struct_0(sK0))
    | ~ spl9_7
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f1133,f145])).

fof(f1133,plain,
    ( ~ m1_subset_1(sK8(sK6(sK0,sK1)),k2_struct_0(sK0))
    | m1_subset_1(sK2(sK8(sK6(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_7
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f1129,f145])).

fof(f1129,plain,
    ( ~ m1_subset_1(sK8(sK6(sK0,sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK2(sK8(sK6(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_44 ),
    inference(resolution,[],[f1125,f51])).

fof(f51,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | m1_subset_1(sK2(X2),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1172,plain,
    ( spl9_48
    | ~ spl9_25
    | spl9_30
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f1118,f757,f753,f471,f1169])).

fof(f753,plain,
    ( spl9_30
  <=> v1_tdlat_3(sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f757,plain,
    ( spl9_31
  <=> v2_pre_topc(sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f1118,plain,
    ( sK7(sK6(sK0,sK1)) = k1_tarski(sK8(sK6(sK0,sK1)))
    | ~ spl9_25
    | spl9_30
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f1117,f758])).

fof(f758,plain,
    ( v2_pre_topc(sK6(sK0,sK1))
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f757])).

fof(f1117,plain,
    ( sK7(sK6(sK0,sK1)) = k1_tarski(sK8(sK6(sK0,sK1)))
    | ~ v2_pre_topc(sK6(sK0,sK1))
    | ~ spl9_25
    | spl9_30 ),
    inference(subsumption_resolution,[],[f1107,f473])).

fof(f1107,plain,
    ( ~ l1_pre_topc(sK6(sK0,sK1))
    | sK7(sK6(sK0,sK1)) = k1_tarski(sK8(sK6(sK0,sK1)))
    | ~ v2_pre_topc(sK6(sK0,sK1))
    | spl9_30 ),
    inference(resolution,[],[f754,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | sK7(X0) = k1_tarski(sK8(X0))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k1_tarski(X2) = X1
                 => v3_pre_topc(X1,X0) ) ) )
       => v1_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tdlat_3)).

fof(f754,plain,
    ( ~ v1_tdlat_3(sK6(sK0,sK1))
    | spl9_30 ),
    inference(avatar_component_clause,[],[f753])).

fof(f1162,plain,
    ( spl9_47
    | ~ spl9_9
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f1153,f1123,f182,f1159])).

fof(f1153,plain,
    ( m1_subset_1(sK8(sK6(sK0,sK1)),k2_struct_0(sK0))
    | ~ spl9_9
    | ~ spl9_44 ),
    inference(resolution,[],[f1130,f184])).

fof(f1130,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | m1_subset_1(sK8(sK6(sK0,sK1)),X0) )
    | ~ spl9_44 ),
    inference(resolution,[],[f1125,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f1147,plain,
    ( ~ spl9_46
    | ~ spl9_25
    | spl9_30
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f1120,f757,f753,f471,f1144])).

fof(f1144,plain,
    ( spl9_46
  <=> v3_pre_topc(sK7(sK6(sK0,sK1)),sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f1120,plain,
    ( ~ v3_pre_topc(sK7(sK6(sK0,sK1)),sK6(sK0,sK1))
    | ~ spl9_25
    | spl9_30
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f1119,f758])).

fof(f1119,plain,
    ( ~ v3_pre_topc(sK7(sK6(sK0,sK1)),sK6(sK0,sK1))
    | ~ v2_pre_topc(sK6(sK0,sK1))
    | ~ spl9_25
    | spl9_30 ),
    inference(subsumption_resolution,[],[f1108,f473])).

fof(f1108,plain,
    ( ~ l1_pre_topc(sK6(sK0,sK1))
    | ~ v3_pre_topc(sK7(sK6(sK0,sK1)),sK6(sK0,sK1))
    | ~ v2_pre_topc(sK6(sK0,sK1))
    | spl9_30 ),
    inference(resolution,[],[f754,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(sK7(X0),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1126,plain,
    ( spl9_44
    | spl9_24
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f1121,f761,f427,f1123])).

fof(f761,plain,
    ( spl9_32
  <=> m1_subset_1(sK8(sK6(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f1121,plain,
    ( r2_hidden(sK8(sK6(sK0,sK1)),sK1)
    | spl9_24
    | ~ spl9_32 ),
    inference(resolution,[],[f763,f1064])).

fof(f1064,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK1)
        | r2_hidden(X1,sK1) )
    | spl9_24 ),
    inference(resolution,[],[f429,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f763,plain,
    ( m1_subset_1(sK8(sK6(sK0,sK1)),sK1)
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f761])).

fof(f1103,plain,
    ( spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_21
    | spl9_24
    | ~ spl9_30 ),
    inference(avatar_contradiction_clause,[],[f1102])).

fof(f1102,plain,
    ( $false
    | spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_21
    | spl9_24
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f1100,f755])).

fof(f755,plain,
    ( v1_tdlat_3(sK6(sK0,sK1))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f753])).

fof(f1100,plain,
    ( ~ v1_tdlat_3(sK6(sK0,sK1))
    | spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_21
    | spl9_24 ),
    inference(subsumption_resolution,[],[f1099,f429])).

fof(f1099,plain,
    ( ~ v1_tdlat_3(sK6(sK0,sK1))
    | v1_xboole_0(sK1)
    | spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1098,f184])).

fof(f1098,plain,
    ( ~ v1_tdlat_3(sK6(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f900,f116])).

fof(f116,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl9_4
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f900,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_tdlat_3(sK6(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(duplicate_literal_removal,[],[f899])).

fof(f899,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_tdlat_3(sK6(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(superposition,[],[f469,f384])).

fof(f469,plain,
    ( ! [X0] :
        ( v2_tex_2(u1_struct_0(sK6(sK0,X0)),sK0)
        | ~ v1_tdlat_3(sK6(sK0,X0))
        | ~ m1_subset_1(u1_struct_0(sK6(sK0,X0)),k1_zfmisc_1(k2_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl9_1
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f468,f204])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK6(sK0,X0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl9_1
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f203,f145])).

fof(f203,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_struct_0(sK6(sK0,X0)) )
    | spl9_1
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f118,f111])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_struct_0(sK6(sK0,X0)) )
    | spl9_1 ),
    inference(resolution,[],[f101,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(sK6(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f468,plain,
    ( ! [X0] :
        ( v2_struct_0(sK6(sK0,X0))
        | ~ m1_subset_1(u1_struct_0(sK6(sK0,X0)),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_tdlat_3(sK6(sK0,X0))
        | v2_tex_2(u1_struct_0(sK6(sK0,X0)),sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl9_1
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(resolution,[],[f170,f223])).

fof(f170,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | ~ m1_subset_1(u1_struct_0(X5),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_tdlat_3(X5)
        | v2_tex_2(u1_struct_0(X5),sK0) )
    | spl9_1
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f169,f101])).

fof(f169,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(u1_struct_0(X5),k1_zfmisc_1(k2_struct_0(sK0)))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(sK0)
        | ~ v1_tdlat_3(X5)
        | v2_tex_2(u1_struct_0(X5),sK0) )
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f156,f111])).

fof(f156,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(u1_struct_0(X5),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(sK0)
        | ~ v1_tdlat_3(X5)
        | v2_tex_2(u1_struct_0(X5),sK0) )
    | ~ spl9_7 ),
    inference(superposition,[],[f97,f145])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f1095,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_9
    | spl9_24
    | spl9_31 ),
    inference(avatar_contradiction_clause,[],[f1094])).

fof(f1094,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_9
    | spl9_24
    | spl9_31 ),
    inference(subsumption_resolution,[],[f1055,f429])).

fof(f1055,plain,
    ( v1_xboole_0(sK1)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_9
    | spl9_31 ),
    inference(subsumption_resolution,[],[f770,f184])).

fof(f770,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_7
    | spl9_31 ),
    inference(resolution,[],[f759,f230])).

fof(f230,plain,
    ( ! [X0] :
        ( v2_pre_topc(sK6(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v1_xboole_0(X0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(resolution,[],[f223,f129])).

fof(f129,plain,
    ( ! [X8] :
        ( ~ m1_pre_topc(X8,sK0)
        | v2_pre_topc(X8) )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f128,f106])).

fof(f106,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl9_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f128,plain,
    ( ! [X8] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X8,sK0)
        | v2_pre_topc(X8) )
    | ~ spl9_3 ),
    inference(resolution,[],[f111,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f759,plain,
    ( ~ v2_pre_topc(sK6(sK0,sK1))
    | spl9_31 ),
    inference(avatar_component_clause,[],[f757])).

fof(f1050,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_6
    | ~ spl9_24 ),
    inference(avatar_contradiction_clause,[],[f1049])).

fof(f1049,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_6
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f1048,f106])).

fof(f1048,plain,
    ( ~ v2_pre_topc(sK0)
    | spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_6
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f1047,f138])).

fof(f1047,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f1046,f101])).

fof(f1046,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl9_3
    | spl9_4
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f1045,f111])).

fof(f1045,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | spl9_4
    | ~ spl9_24 ),
    inference(resolution,[],[f476,f116])).

fof(f476,plain,
    ( ! [X0] :
        ( v2_tex_2(sK1,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0) )
    | ~ spl9_24 ),
    inference(resolution,[],[f428,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f428,plain,
    ( v1_xboole_0(sK1)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f427])).

fof(f764,plain,
    ( spl9_30
    | ~ spl9_31
    | spl9_32
    | ~ spl9_21
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f740,f471,f382,f761,f757,f753])).

fof(f740,plain,
    ( m1_subset_1(sK8(sK6(sK0,sK1)),sK1)
    | ~ v2_pre_topc(sK6(sK0,sK1))
    | v1_tdlat_3(sK6(sK0,sK1))
    | ~ spl9_21
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f391,f473])).

fof(f391,plain,
    ( m1_subset_1(sK8(sK6(sK0,sK1)),sK1)
    | ~ l1_pre_topc(sK6(sK0,sK1))
    | ~ v2_pre_topc(sK6(sK0,sK1))
    | v1_tdlat_3(sK6(sK0,sK1))
    | ~ spl9_21 ),
    inference(superposition,[],[f83,f384])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(X0),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f554,plain,
    ( spl9_27
    | ~ spl9_21
    | ~ spl9_23
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f549,f533,f423,f382,f551])).

fof(f423,plain,
    ( spl9_23
  <=> l1_struct_0(sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f549,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl9_21
    | ~ spl9_23
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f548,f535])).

fof(f548,plain,
    ( m1_subset_1(k2_struct_0(sK6(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl9_21
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f387,f424])).

fof(f424,plain,
    ( l1_struct_0(sK6(sK0,sK1))
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f423])).

fof(f387,plain,
    ( m1_subset_1(k2_struct_0(sK6(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ l1_struct_0(sK6(sK0,sK1))
    | ~ spl9_21 ),
    inference(superposition,[],[f60,f384])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f536,plain,
    ( spl9_26
    | ~ spl9_21
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f531,f423,f382,f533])).

fof(f531,plain,
    ( sK1 = k2_struct_0(sK6(sK0,sK1))
    | ~ spl9_21
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f530,f384])).

fof(f530,plain,
    ( u1_struct_0(sK6(sK0,sK1)) = k2_struct_0(sK6(sK0,sK1))
    | ~ spl9_23 ),
    inference(resolution,[],[f424,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f504,plain,
    ( spl9_23
    | ~ spl9_25 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | spl9_23
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f495,f425])).

fof(f425,plain,
    ( ~ l1_struct_0(sK6(sK0,sK1))
    | spl9_23 ),
    inference(avatar_component_clause,[],[f423])).

fof(f495,plain,
    ( l1_struct_0(sK6(sK0,sK1))
    | ~ spl9_25 ),
    inference(resolution,[],[f473,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f489,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | spl9_25 ),
    inference(avatar_contradiction_clause,[],[f488])).

fof(f488,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | spl9_25 ),
    inference(subsumption_resolution,[],[f487,f184])).

fof(f487,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | spl9_25 ),
    inference(subsumption_resolution,[],[f486,f138])).

fof(f486,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_7
    | spl9_25 ),
    inference(subsumption_resolution,[],[f485,f101])).

fof(f485,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_7
    | spl9_25 ),
    inference(subsumption_resolution,[],[f484,f111])).

fof(f484,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_7
    | spl9_25 ),
    inference(subsumption_resolution,[],[f483,f106])).

fof(f483,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_7
    | spl9_25 ),
    inference(subsumption_resolution,[],[f482,f472])).

fof(f472,plain,
    ( ~ l1_pre_topc(sK6(sK0,sK1))
    | spl9_25 ),
    inference(avatar_component_clause,[],[f471])).

fof(f482,plain,
    ( l1_pre_topc(sK6(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_7 ),
    inference(resolution,[],[f271,f116])).

fof(f271,plain,
    ( ! [X2,X1] :
        ( v2_tex_2(X1,X2)
        | l1_pre_topc(sK6(sK0,X1))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl9_1
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(resolution,[],[f231,f76])).

fof(f231,plain,
    ( ! [X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | l1_pre_topc(sK6(sK0,X1)) )
    | spl9_1
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(resolution,[],[f223,f125])).

fof(f385,plain,
    ( spl9_21
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f326,f182,f143,f136,f114,f109,f104,f99,f382])).

fof(f326,plain,
    ( sK1 = u1_struct_0(sK6(sK0,sK1))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f325,f184])).

fof(f325,plain,
    ( sK1 = u1_struct_0(sK6(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f324,f138])).

fof(f324,plain,
    ( sK1 = u1_struct_0(sK6(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f323,f101])).

fof(f323,plain,
    ( sK1 = u1_struct_0(sK6(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f322,f111])).

fof(f322,plain,
    ( sK1 = u1_struct_0(sK6(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f321,f106])).

fof(f321,plain,
    ( sK1 = u1_struct_0(sK6(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_7 ),
    inference(resolution,[],[f241,f116])).

fof(f241,plain,
    ( ! [X2,X1] :
        ( v2_tex_2(X1,X2)
        | u1_struct_0(sK6(sK0,X1)) = X1
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl9_1
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(resolution,[],[f234,f76])).

fof(f234,plain,
    ( ! [X2] :
        ( v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
        | u1_struct_0(sK6(sK0,X2)) = X2 )
    | spl9_1
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f233,f145])).

fof(f233,plain,
    ( ! [X2] :
        ( v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK6(sK0,X2)) = X2 )
    | spl9_1
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f120,f111])).

fof(f120,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK6(sK0,X2)) = X2 )
    | spl9_1 ),
    inference(resolution,[],[f101,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK6(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f185,plain,
    ( spl9_9
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f147,f143,f136,f182])).

fof(f147,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(superposition,[],[f138,f145])).

fof(f178,plain,
    ( ~ spl9_8
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f161,f143,f131,f99,f175])).

fof(f131,plain,
    ( spl9_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f161,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f160,f101])).

fof(f160,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f151,f133])).

fof(f133,plain,
    ( l1_struct_0(sK0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f151,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_7 ),
    inference(superposition,[],[f75,f145])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f146,plain,
    ( spl9_7
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f140,f131,f143])).

fof(f140,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl9_5 ),
    inference(resolution,[],[f133,f59])).

fof(f139,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f54,f136])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f134,plain,
    ( spl9_5
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f121,f109,f131])).

fof(f121,plain,
    ( l1_struct_0(sK0)
    | ~ spl9_3 ),
    inference(resolution,[],[f111,f61])).

fof(f117,plain,(
    ~ spl9_4 ),
    inference(avatar_split_clause,[],[f55,f114])).

fof(f55,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f112,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f58,f109])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f107,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f57,f104])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f102,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f56,f99])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
