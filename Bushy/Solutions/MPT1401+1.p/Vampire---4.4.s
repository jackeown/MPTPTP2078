%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t31_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:53 EDT 2019

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 320 expanded)
%              Number of leaves         :   36 ( 139 expanded)
%              Depth                    :   14
%              Number of atoms          :  730 (2165 expanded)
%              Number of equality atoms :   67 ( 225 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2532,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f137,f144,f165,f172,f179,f186,f193,f200,f207,f264,f435,f446,f466,f485,f534,f590,f648,f694,f821,f961,f2511,f2527])).

fof(f2527,plain,
    ( spl9_35
    | ~ spl9_114
    | ~ spl9_322 ),
    inference(avatar_contradiction_clause,[],[f2526])).

fof(f2526,plain,
    ( $false
    | ~ spl9_35
    | ~ spl9_114
    | ~ spl9_322 ),
    inference(subsumption_resolution,[],[f2518,f263])).

fof(f263,plain,
    ( ~ r1_tarski(k1_connsp_2(sK0,sK1),sK2)
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl9_35
  <=> ~ r1_tarski(k1_connsp_2(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f2518,plain,
    ( r1_tarski(k1_connsp_2(sK0,sK1),sK2)
    | ~ spl9_114
    | ~ spl9_322 ),
    inference(resolution,[],[f2509,f820])).

fof(f820,plain,
    ( r2_hidden(sK2,sK4(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_114 ),
    inference(avatar_component_clause,[],[f819])).

fof(f819,plain,
    ( spl9_114
  <=> r2_hidden(sK2,sK4(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_114])])).

fof(f2509,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK4(sK0,sK1,k1_connsp_2(sK0,sK1)))
        | r1_tarski(k1_connsp_2(sK0,sK1),X1) )
    | ~ spl9_322 ),
    inference(avatar_component_clause,[],[f2508])).

fof(f2508,plain,
    ( spl9_322
  <=> ! [X1] :
        ( r1_tarski(k1_connsp_2(sK0,sK1),X1)
        | ~ r2_hidden(X1,sK4(sK0,sK1,k1_connsp_2(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_322])])).

fof(f2511,plain,
    ( spl9_322
    | ~ spl9_134 ),
    inference(avatar_split_clause,[],[f1635,f959,f2508])).

fof(f959,plain,
    ( spl9_134
  <=> k1_connsp_2(sK0,sK1) = k1_setfam_1(sK4(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).

fof(f1635,plain,
    ( ! [X4] :
        ( r1_tarski(k1_connsp_2(sK0,sK1),X4)
        | ~ r2_hidden(X4,sK4(sK0,sK1,k1_connsp_2(sK0,sK1))) )
    | ~ spl9_134 ),
    inference(superposition,[],[f93,f960])).

fof(f960,plain,
    ( k1_connsp_2(sK0,sK1) = k1_setfam_1(sK4(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_134 ),
    inference(avatar_component_clause,[],[f959])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t31_connsp_2.p',t4_setfam_1)).

fof(f961,plain,
    ( spl9_134
    | ~ spl9_72
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f930,f588,f483,f959])).

fof(f483,plain,
    ( spl9_72
  <=> r1_tarski(sK4(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f588,plain,
    ( spl9_96
  <=> k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK4(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).

fof(f930,plain,
    ( k1_connsp_2(sK0,sK1) = k1_setfam_1(sK4(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_72
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f927,f589])).

fof(f589,plain,
    ( k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK4(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_96 ),
    inference(avatar_component_clause,[],[f588])).

fof(f927,plain,
    ( k6_setfam_1(u1_struct_0(sK0),sK4(sK0,sK1,k1_connsp_2(sK0,sK1))) = k1_setfam_1(sK4(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_72 ),
    inference(resolution,[],[f484,f265])).

fof(f265,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_zfmisc_1(X0))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(resolution,[],[f95,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t31_connsp_2.p',t3_subset)).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t31_connsp_2.p',redefinition_k6_setfam_1)).

fof(f484,plain,
    ( r1_tarski(sK4(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_72 ),
    inference(avatar_component_clause,[],[f483])).

fof(f821,plain,
    ( spl9_114
    | ~ spl9_14
    | ~ spl9_104
    | ~ spl9_106 ),
    inference(avatar_split_clause,[],[f701,f692,f646,f177,f819])).

fof(f177,plain,
    ( spl9_14
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f646,plain,
    ( spl9_104
  <=> m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_104])])).

fof(f692,plain,
    ( spl9_106
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,sK4(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f701,plain,
    ( r2_hidden(sK2,sK4(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_14
    | ~ spl9_104
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f699,f647])).

fof(f647,plain,
    ( m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_104 ),
    inference(avatar_component_clause,[],[f646])).

fof(f699,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,sK4(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_14
    | ~ spl9_106 ),
    inference(resolution,[],[f693,f178])).

fof(f178,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f177])).

fof(f693,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,sK4(sK0,X0,k1_connsp_2(sK0,X0))) )
    | ~ spl9_106 ),
    inference(avatar_component_clause,[],[f692])).

fof(f694,plain,
    ( spl9_106
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_18
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f538,f532,f191,f170,f163,f692])).

fof(f163,plain,
    ( spl9_10
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f170,plain,
    ( spl9_12
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f191,plain,
    ( spl9_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f532,plain,
    ( spl9_84
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ v4_pre_topc(X1,sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,sK4(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f538,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,sK4(sK0,X0,k1_connsp_2(sK0,X0))) )
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_18
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f537,f192])).

fof(f192,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f191])).

fof(f537,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,sK4(sK0,X0,k1_connsp_2(sK0,X0))) )
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f536,f164])).

fof(f164,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f163])).

fof(f536,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v3_pre_topc(sK2,sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,sK4(sK0,X0,k1_connsp_2(sK0,X0))) )
    | ~ spl9_12
    | ~ spl9_84 ),
    inference(resolution,[],[f533,f171])).

fof(f171,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f170])).

fof(f533,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X1,sK0)
        | ~ r2_hidden(X0,X1)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,sK4(sK0,X0,k1_connsp_2(sK0,X0))) )
    | ~ spl9_84 ),
    inference(avatar_component_clause,[],[f532])).

fof(f648,plain,
    ( spl9_104
    | ~ spl9_66
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f599,f588,f464,f646])).

fof(f464,plain,
    ( spl9_66
  <=> m1_subset_1(sK4(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f599,plain,
    ( m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_66
    | ~ spl9_96 ),
    inference(subsumption_resolution,[],[f597,f465])).

fof(f465,plain,
    ( m1_subset_1(sK4(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_66 ),
    inference(avatar_component_clause,[],[f464])).

fof(f597,plain,
    ( m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_96 ),
    inference(superposition,[],[f96,f589])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t31_connsp_2.p',dt_k6_setfam_1)).

fof(f590,plain,
    ( spl9_96
    | ~ spl9_16
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f452,f444,f184,f588])).

fof(f184,plain,
    ( spl9_16
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f444,plain,
    ( spl9_64
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK4(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f452,plain,
    ( k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK4(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_16
    | ~ spl9_64 ),
    inference(resolution,[],[f445,f185])).

fof(f185,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f184])).

fof(f445,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK4(sK0,X0,k1_connsp_2(sK0,X0))) )
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f444])).

fof(f534,plain,
    ( spl9_84
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f336,f142,f135,f128,f532])).

fof(f128,plain,
    ( spl9_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f135,plain,
    ( spl9_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f142,plain,
    ( spl9_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f336,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v4_pre_topc(X1,sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,sK4(sK0,X0,k1_connsp_2(sK0,X0))) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f335,f129])).

fof(f129,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f128])).

fof(f335,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v4_pre_topc(X1,sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,sK4(sK0,X0,k1_connsp_2(sK0,X0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f334,f143])).

fof(f143,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f142])).

fof(f334,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v4_pre_topc(X1,sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | r2_hidden(X1,sK4(sK0,X0,k1_connsp_2(sK0,X0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2 ),
    inference(resolution,[],[f332,f136])).

fof(f136,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f332,plain,(
    ! [X6,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,X6)
      | ~ v4_pre_topc(X6,X0)
      | ~ v3_pre_topc(X6,X0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X6,sK4(X0,X1,k1_connsp_2(X0,X1)))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f115,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t31_connsp_2.p',t4_subset)).

fof(f115,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,sK4(X0,X1,k1_connsp_2(X0,X1)))
      | ~ r2_hidden(X1,X6)
      | ~ v4_pre_topc(X6,X0)
      | ~ v3_pre_topc(X6,X0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,sK4(X0,X1,X2))
      | ~ r2_hidden(X1,X6)
      | ~ v4_pre_topc(X6,X0)
      | ~ v3_pre_topc(X6,X0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_connsp_2(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_connsp_2(X0,X1) = X2
                  | ! [X3] :
                      ( k6_setfam_1(u1_struct_0(X0),X3) != X2
                      | ( ( ~ r2_hidden(X1,sK3(X0,X1,X3))
                          | ~ v4_pre_topc(sK3(X0,X1,X3),X0)
                          | ~ v3_pre_topc(sK3(X0,X1,X3),X0)
                          | ~ r2_hidden(sK3(X0,X1,X3),X3) )
                        & ( ( r2_hidden(X1,sK3(X0,X1,X3))
                            & v4_pre_topc(sK3(X0,X1,X3),X0)
                            & v3_pre_topc(sK3(X0,X1,X3),X0) )
                          | r2_hidden(sK3(X0,X1,X3),X3) )
                        & m1_subset_1(sK3(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
                & ( ( k6_setfam_1(u1_struct_0(X0),sK4(X0,X1,X2)) = X2
                    & ! [X6] :
                        ( ( ( r2_hidden(X6,sK4(X0,X1,X2))
                            | ~ r2_hidden(X1,X6)
                            | ~ v4_pre_topc(X6,X0)
                            | ~ v3_pre_topc(X6,X0) )
                          & ( ( r2_hidden(X1,X6)
                              & v4_pre_topc(X6,X0)
                              & v3_pre_topc(X6,X0) )
                            | ~ r2_hidden(X6,sK4(X0,X1,X2)) ) )
                        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | k1_connsp_2(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).

fof(f55,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(X1,X4)
            | ~ v4_pre_topc(X4,X0)
            | ~ v3_pre_topc(X4,X0)
            | ~ r2_hidden(X4,X3) )
          & ( ( r2_hidden(X1,X4)
              & v4_pre_topc(X4,X0)
              & v3_pre_topc(X4,X0) )
            | r2_hidden(X4,X3) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r2_hidden(X1,sK3(X0,X1,X3))
          | ~ v4_pre_topc(sK3(X0,X1,X3),X0)
          | ~ v3_pre_topc(sK3(X0,X1,X3),X0)
          | ~ r2_hidden(sK3(X0,X1,X3),X3) )
        & ( ( r2_hidden(X1,sK3(X0,X1,X3))
            & v4_pre_topc(sK3(X0,X1,X3),X0)
            & v3_pre_topc(sK3(X0,X1,X3),X0) )
          | r2_hidden(sK3(X0,X1,X3),X3) )
        & m1_subset_1(sK3(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k6_setfam_1(u1_struct_0(X0),X5) = X2
          & ! [X6] :
              ( ( ( r2_hidden(X6,X5)
                  | ~ r2_hidden(X1,X6)
                  | ~ v4_pre_topc(X6,X0)
                  | ~ v3_pre_topc(X6,X0) )
                & ( ( r2_hidden(X1,X6)
                    & v4_pre_topc(X6,X0)
                    & v3_pre_topc(X6,X0) )
                  | ~ r2_hidden(X6,X5) ) )
              | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k6_setfam_1(u1_struct_0(X0),sK4(X0,X1,X2)) = X2
        & ! [X6] :
            ( ( ( r2_hidden(X6,sK4(X0,X1,X2))
                | ~ r2_hidden(X1,X6)
                | ~ v4_pre_topc(X6,X0)
                | ~ v3_pre_topc(X6,X0) )
              & ( ( r2_hidden(X1,X6)
                  & v4_pre_topc(X6,X0)
                  & v3_pre_topc(X6,X0) )
                | ~ r2_hidden(X6,sK4(X0,X1,X2)) ) )
            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_connsp_2(X0,X1) = X2
                  | ! [X3] :
                      ( k6_setfam_1(u1_struct_0(X0),X3) != X2
                      | ? [X4] :
                          ( ( ~ r2_hidden(X1,X4)
                            | ~ v4_pre_topc(X4,X0)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ r2_hidden(X4,X3) )
                          & ( ( r2_hidden(X1,X4)
                              & v4_pre_topc(X4,X0)
                              & v3_pre_topc(X4,X0) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
                & ( ? [X5] :
                      ( k6_setfam_1(u1_struct_0(X0),X5) = X2
                      & ! [X6] :
                          ( ( ( r2_hidden(X6,X5)
                              | ~ r2_hidden(X1,X6)
                              | ~ v4_pre_topc(X6,X0)
                              | ~ v3_pre_topc(X6,X0) )
                            & ( ( r2_hidden(X1,X6)
                                & v4_pre_topc(X6,X0)
                                & v3_pre_topc(X6,X0) )
                              | ~ r2_hidden(X6,X5) ) )
                          | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                      & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | k1_connsp_2(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_connsp_2(X0,X1) = X2
                  | ! [X3] :
                      ( k6_setfam_1(u1_struct_0(X0),X3) != X2
                      | ? [X4] :
                          ( ( ~ r2_hidden(X1,X4)
                            | ~ v4_pre_topc(X4,X0)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ r2_hidden(X4,X3) )
                          & ( ( r2_hidden(X1,X4)
                              & v4_pre_topc(X4,X0)
                              & v3_pre_topc(X4,X0) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
                & ( ? [X3] :
                      ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                      & ! [X4] :
                          ( ( ( r2_hidden(X4,X3)
                              | ~ r2_hidden(X1,X4)
                              | ~ v4_pre_topc(X4,X0)
                              | ~ v3_pre_topc(X4,X0) )
                            & ( ( r2_hidden(X1,X4)
                                & v4_pre_topc(X4,X0)
                                & v3_pre_topc(X4,X0) )
                              | ~ r2_hidden(X4,X3) ) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | k1_connsp_2(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_connsp_2(X0,X1) = X2
                  | ! [X3] :
                      ( k6_setfam_1(u1_struct_0(X0),X3) != X2
                      | ? [X4] :
                          ( ( ~ r2_hidden(X1,X4)
                            | ~ v4_pre_topc(X4,X0)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ r2_hidden(X4,X3) )
                          & ( ( r2_hidden(X1,X4)
                              & v4_pre_topc(X4,X0)
                              & v3_pre_topc(X4,X0) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
                & ( ? [X3] :
                      ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                      & ! [X4] :
                          ( ( ( r2_hidden(X4,X3)
                              | ~ r2_hidden(X1,X4)
                              | ~ v4_pre_topc(X4,X0)
                              | ~ v3_pre_topc(X4,X0) )
                            & ( ( r2_hidden(X1,X4)
                                & v4_pre_topc(X4,X0)
                                & v3_pre_topc(X4,X0) )
                              | ~ r2_hidden(X4,X3) ) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | k1_connsp_2(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t31_connsp_2.p',d7_connsp_2)).

fof(f485,plain,
    ( spl9_72
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f473,f464,f483])).

fof(f473,plain,
    ( r1_tarski(sK4(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_66 ),
    inference(resolution,[],[f465,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f466,plain,
    ( spl9_66
    | ~ spl9_16
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f436,f433,f184,f464])).

fof(f433,plain,
    ( spl9_62
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK0,X0,k1_connsp_2(sK0,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f436,plain,
    ( m1_subset_1(sK4(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_16
    | ~ spl9_62 ),
    inference(resolution,[],[f434,f185])).

fof(f434,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK0,X0,k1_connsp_2(sK0,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f433])).

fof(f446,plain,
    ( spl9_64
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f297,f142,f135,f128,f444])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK4(sK0,X0,k1_connsp_2(sK0,X0))) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f296,f129])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK4(sK0,X0,k1_connsp_2(sK0,X0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f295,f143])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK4(sK0,X0,k1_connsp_2(sK0,X0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2 ),
    inference(resolution,[],[f287,f136])).

fof(f287,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK4(X0,X1,k1_connsp_2(X0,X1)))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f114,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t31_connsp_2.p',dt_k1_connsp_2)).

fof(f114,plain,(
    ! [X0,X1] :
      ( k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK4(X0,X1,k1_connsp_2(X0,X1)))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k6_setfam_1(u1_struct_0(X0),sK4(X0,X1,X2)) = X2
      | k1_connsp_2(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f435,plain,
    ( spl9_62
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f283,f142,f135,f128,f433])).

fof(f283,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK0,X0,k1_connsp_2(sK0,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f282,f129])).

fof(f282,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK0,X0,k1_connsp_2(sK0,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f281,f143])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | m1_subset_1(sK4(sK0,X0,k1_connsp_2(sK0,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl9_2 ),
    inference(resolution,[],[f276,f136])).

fof(f276,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f119,f97])).

fof(f119,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | k1_connsp_2(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f264,plain,
    ( ~ spl9_35
    | ~ spl9_20
    | spl9_23 ),
    inference(avatar_split_clause,[],[f255,f205,f198,f262])).

fof(f198,plain,
    ( spl9_20
  <=> r1_tarski(sK2,k1_connsp_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f205,plain,
    ( spl9_23
  <=> k1_connsp_2(sK0,sK1) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f255,plain,
    ( ~ r1_tarski(k1_connsp_2(sK0,sK1),sK2)
    | ~ spl9_20
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f252,f206])).

fof(f206,plain,
    ( k1_connsp_2(sK0,sK1) != sK2
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f205])).

fof(f252,plain,
    ( ~ r1_tarski(k1_connsp_2(sK0,sK1),sK2)
    | k1_connsp_2(sK0,sK1) = sK2
    | ~ spl9_20 ),
    inference(resolution,[],[f100,f199])).

fof(f199,plain,
    ( r1_tarski(sK2,k1_connsp_2(sK0,sK1))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f198])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t31_connsp_2.p',d10_xboole_0)).

fof(f207,plain,(
    ~ spl9_23 ),
    inference(avatar_split_clause,[],[f76,f205])).

fof(f76,plain,(
    k1_connsp_2(sK0,sK1) != sK2 ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( k1_connsp_2(sK0,sK1) != sK2
    & r1_tarski(sK2,k1_connsp_2(sK0,sK1))
    & r2_hidden(sK1,sK2)
    & v4_pre_topc(sK2,sK0)
    & v3_pre_topc(sK2,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f50,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_connsp_2(X0,X1) != X2
                & r1_tarski(X2,k1_connsp_2(X0,X1))
                & r2_hidden(X1,X2)
                & v4_pre_topc(X2,X0)
                & v3_pre_topc(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(sK0,X1) != X2
              & r1_tarski(X2,k1_connsp_2(sK0,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,sK0)
              & v3_pre_topc(X2,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(X0,X1) != X2
              & r1_tarski(X2,k1_connsp_2(X0,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,X0)
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_connsp_2(X0,sK1) != X2
            & r1_tarski(X2,k1_connsp_2(X0,sK1))
            & r2_hidden(sK1,X2)
            & v4_pre_topc(X2,X0)
            & v3_pre_topc(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_connsp_2(X0,X1) != X2
          & r1_tarski(X2,k1_connsp_2(X0,X1))
          & r2_hidden(X1,X2)
          & v4_pre_topc(X2,X0)
          & v3_pre_topc(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_connsp_2(X0,X1) != sK2
        & r1_tarski(sK2,k1_connsp_2(X0,X1))
        & r2_hidden(X1,sK2)
        & v4_pre_topc(sK2,X0)
        & v3_pre_topc(sK2,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(X0,X1) != X2
              & r1_tarski(X2,k1_connsp_2(X0,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,X0)
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(X0,X1) != X2
              & r1_tarski(X2,k1_connsp_2(X0,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,X0)
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X2,k1_connsp_2(X0,X1))
                    & r2_hidden(X1,X2)
                    & v4_pre_topc(X2,X0)
                    & v3_pre_topc(X2,X0) )
                 => k1_connsp_2(X0,X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,k1_connsp_2(X0,X1))
                  & r2_hidden(X1,X2)
                  & v4_pre_topc(X2,X0)
                  & v3_pre_topc(X2,X0) )
               => k1_connsp_2(X0,X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t31_connsp_2.p',t31_connsp_2)).

fof(f200,plain,(
    spl9_20 ),
    inference(avatar_split_clause,[],[f75,f198])).

fof(f75,plain,(
    r1_tarski(sK2,k1_connsp_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f193,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f71,f191])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f186,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f70,f184])).

fof(f70,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f179,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f74,f177])).

fof(f74,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f172,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f73,f170])).

fof(f73,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f165,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f72,f163])).

fof(f72,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f144,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f69,f142])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f137,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f68,f135])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f130,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f67,f128])).

fof(f67,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
