%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 303 expanded)
%              Number of leaves         :   41 ( 129 expanded)
%              Depth                    :   11
%              Number of atoms          :  438 ( 845 expanded)
%              Number of equality atoms :   64 ( 110 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1057,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f75,f80,f85,f95,f103,f155,f157,f177,f181,f217,f300,f309,f323,f337,f339,f430,f578,f723,f740,f993,f1053,f1056])).

fof(f1056,plain,
    ( sK1 != k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))
    | k5_xboole_0(k2_struct_0(sK0),sK1) != k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))
    | k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) != k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1053,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_14
    | spl3_33
    | ~ spl3_102 ),
    inference(avatar_contradiction_clause,[],[f1052])).

fof(f1052,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_14
    | spl3_33
    | ~ spl3_102 ),
    inference(subsumption_resolution,[],[f1051,f336])).

fof(f336,plain,
    ( ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl3_33
  <=> v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f1051,plain,
    ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_102 ),
    inference(forward_demodulation,[],[f1050,f992])).

fof(f992,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl3_102 ),
    inference(avatar_component_clause,[],[f990])).

fof(f990,plain,
    ( spl3_102
  <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_102])])).

fof(f1050,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f1041,f68])).

fof(f68,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1041,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(resolution,[],[f178,f176])).

fof(f176,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl3_14
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f178,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X1,sK0)
        | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1),sK0) )
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f165,f84])).

fof(f84,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f165,plain,
    ( ! [X1] :
        ( v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1),sK0)
        | ~ v4_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_6 ),
    inference(superposition,[],[f47,f101])).

fof(f101,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_6
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f993,plain,
    ( spl3_102
    | ~ spl3_55
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f988,f735,f573,f990])).

fof(f573,plain,
    ( spl3_55
  <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f735,plain,
    ( spl3_73
  <=> k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f988,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl3_55
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f575,f737])).

fof(f737,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f735])).

fof(f575,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f573])).

fof(f740,plain,
    ( spl3_73
    | ~ spl3_71 ),
    inference(avatar_split_clause,[],[f739,f720,f735])).

fof(f720,plain,
    ( spl3_71
  <=> r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f739,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl3_71 ),
    inference(forward_demodulation,[],[f732,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f732,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)))
    | ~ spl3_71 ),
    inference(resolution,[],[f722,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f722,plain,
    ( r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f720])).

fof(f723,plain,
    ( spl3_71
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f718,f329,f720])).

fof(f329,plain,
    ( spl3_32
  <=> m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f718,plain,
    ( r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | ~ spl3_32 ),
    inference(duplicate_literal_removal,[],[f714])).

fof(f714,plain,
    ( r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | ~ spl3_32 ),
    inference(resolution,[],[f398,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f398,plain,
    ( ! [X2] :
        ( r2_hidden(sK2(k5_xboole_0(k2_struct_0(sK0),sK1),X2),k2_struct_0(sK0))
        | r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),X2) )
    | ~ spl3_32 ),
    inference(resolution,[],[f352,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f352,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k5_xboole_0(k2_struct_0(sK0),sK1))
        | r2_hidden(X3,k2_struct_0(sK0)) )
    | ~ spl3_32 ),
    inference(resolution,[],[f331,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f331,plain,
    ( m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f329])).

fof(f578,plain,
    ( spl3_55
    | ~ spl3_32
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f566,f422,f329,f573])).

fof(f422,plain,
    ( spl3_43
  <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f566,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl3_32
    | ~ spl3_43 ),
    inference(superposition,[],[f424,f340])).

fof(f340,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,k5_xboole_0(k2_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X0,k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl3_32 ),
    inference(unit_resulting_resolution,[],[f331,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f60,f50])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f424,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f422])).

fof(f430,plain,
    ( spl3_43
    | ~ spl3_18
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f429,f320,f214,f422])).

fof(f214,plain,
    ( spl3_18
  <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f320,plain,
    ( spl3_31
  <=> k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f429,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl3_18
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f216,f322])).

fof(f322,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f320])).

fof(f216,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f214])).

fof(f339,plain,
    ( spl3_32
    | ~ spl3_14
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f338,f320,f174,f329])).

fof(f338,plain,
    ( m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_14
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f327,f176])).

fof(f327,plain,
    ( m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_31 ),
    inference(superposition,[],[f54,f322])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f337,plain,
    ( ~ spl3_33
    | spl3_13
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f325,f320,f169,f334])).

fof(f169,plain,
    ( spl3_13
  <=> v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f325,plain,
    ( ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | spl3_13
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f170,f322])).

fof(f170,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f169])).

fof(f323,plain,
    ( spl3_31
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f318,f305,f129,f99,f320])).

fof(f129,plain,
    ( spl3_8
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f305,plain,
    ( spl3_29
  <=> sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f318,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f317,f307])).

fof(f307,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f305])).

fof(f317,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))))
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f131,f101])).

fof(f131,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f309,plain,
    ( spl3_29
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f303,f297,f305])).

fof(f297,plain,
    ( spl3_28
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f303,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))
    | ~ spl3_28 ),
    inference(resolution,[],[f299,f63])).

fof(f299,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f297])).

fof(f300,plain,
    ( spl3_28
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f295,f99,f77,f297])).

fof(f77,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f295,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f228,f59])).

fof(f228,plain,
    ( ! [X2] :
        ( r2_hidden(sK2(sK1,X2),k2_struct_0(sK0))
        | r1_tarski(sK1,X2) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f161,f58])).

fof(f161,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | r2_hidden(X3,k2_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f118,f101])).

fof(f118,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | r2_hidden(X3,u1_struct_0(sK0)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f79,f56])).

fof(f79,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f217,plain,
    ( spl3_18
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f212,f174,f214])).

fof(f212,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f186,f43])).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f186,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0)),sK1) = k9_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0)),k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f44,f176,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f181,plain,
    ( ~ spl3_13
    | spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f180,f99,f71,f169])).

fof(f71,plain,
    ( spl3_2
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f180,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | spl3_2
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f73,f101])).

fof(f73,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f177,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f163,f99,f77,f174])).

fof(f163,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f79,f101])).

fof(f157,plain,
    ( spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f156,f77,f129])).

fof(f156,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f119,f49])).

fof(f119,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))
    | ~ spl3_3 ),
    inference(resolution,[],[f79,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f155,plain,
    ( ~ spl3_12
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f105,f82,f77,f67,f152])).

fof(f152,plain,
    ( spl3_12
  <=> v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f105,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f84,f69,f79,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f103,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f97,f91,f99])).

fof(f91,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f97,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f93,f45])).

fof(f45,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f93,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f95,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f89,f82,f91])).

fof(f89,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f84,f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f85,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f39,f82])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | ~ v4_pre_topc(X1,sK0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | ~ v4_pre_topc(X1,sK0) )
        & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | ~ v4_pre_topc(sK1,sK0) )
      & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f80,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f41,f71,f67])).

fof(f41,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f42,f71,f67])).

fof(f42,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:15:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (21582)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.48  % (21598)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (21598)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f1057,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f74,f75,f80,f85,f95,f103,f155,f157,f177,f181,f217,f300,f309,f323,f337,f339,f430,f578,f723,f740,f993,f1053,f1056])).
% 0.21/0.51  fof(f1056,plain,(
% 0.21/0.51    sK1 != k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) | k5_xboole_0(k2_struct_0(sK0),sK1) != k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) | k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) != k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) | u1_struct_0(sK0) != k2_struct_0(sK0) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f1053,plain,(
% 0.21/0.51    ~spl3_1 | ~spl3_4 | ~spl3_6 | ~spl3_14 | spl3_33 | ~spl3_102),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1052])).
% 0.21/0.51  fof(f1052,plain,(
% 0.21/0.51    $false | (~spl3_1 | ~spl3_4 | ~spl3_6 | ~spl3_14 | spl3_33 | ~spl3_102)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1051,f336])).
% 0.21/0.51  fof(f336,plain,(
% 0.21/0.51    ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | spl3_33),
% 0.21/0.51    inference(avatar_component_clause,[],[f334])).
% 0.21/0.51  fof(f334,plain,(
% 0.21/0.51    spl3_33 <=> v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.51  fof(f1051,plain,(
% 0.21/0.51    v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | (~spl3_1 | ~spl3_4 | ~spl3_6 | ~spl3_14 | ~spl3_102)),
% 0.21/0.51    inference(forward_demodulation,[],[f1050,f992])).
% 0.21/0.51  fof(f992,plain,(
% 0.21/0.51    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) | ~spl3_102),
% 0.21/0.51    inference(avatar_component_clause,[],[f990])).
% 0.21/0.51  fof(f990,plain,(
% 0.21/0.51    spl3_102 <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_102])])).
% 0.21/0.51  fof(f1050,plain,(
% 0.21/0.51    v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | (~spl3_1 | ~spl3_4 | ~spl3_6 | ~spl3_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1041,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    v4_pre_topc(sK1,sK0) | ~spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    spl3_1 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f1041,plain,(
% 0.21/0.51    ~v4_pre_topc(sK1,sK0) | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | (~spl3_4 | ~spl3_6 | ~spl3_14)),
% 0.21/0.51    inference(resolution,[],[f178,f176])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f174])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    spl3_14 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1),sK0)) ) | (~spl3_4 | ~spl3_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f165,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ( ! [X1] : (v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_6),
% 0.21/0.51    inference(superposition,[],[f47,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl3_6 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).
% 0.21/0.51  fof(f993,plain,(
% 0.21/0.51    spl3_102 | ~spl3_55 | ~spl3_73),
% 0.21/0.51    inference(avatar_split_clause,[],[f988,f735,f573,f990])).
% 0.21/0.51  fof(f573,plain,(
% 0.21/0.51    spl3_55 <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.21/0.51  fof(f735,plain,(
% 0.21/0.51    spl3_73 <=> k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 0.21/0.51  fof(f988,plain,(
% 0.21/0.51    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) | (~spl3_55 | ~spl3_73)),
% 0.21/0.51    inference(forward_demodulation,[],[f575,f737])).
% 0.21/0.51  fof(f737,plain,(
% 0.21/0.51    k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) | ~spl3_73),
% 0.21/0.51    inference(avatar_component_clause,[],[f735])).
% 0.21/0.51  fof(f575,plain,(
% 0.21/0.51    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) | ~spl3_55),
% 0.21/0.51    inference(avatar_component_clause,[],[f573])).
% 0.21/0.51  fof(f740,plain,(
% 0.21/0.51    spl3_73 | ~spl3_71),
% 0.21/0.51    inference(avatar_split_clause,[],[f739,f720,f735])).
% 0.21/0.51  fof(f720,plain,(
% 0.21/0.51    spl3_71 <=> r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 0.21/0.51  fof(f739,plain,(
% 0.21/0.51    k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) | ~spl3_71),
% 0.21/0.51    inference(forward_demodulation,[],[f732,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.51  fof(f732,plain,(
% 0.21/0.51    k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))) | ~spl3_71),
% 0.21/0.51    inference(resolution,[],[f722,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f53,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.51  fof(f722,plain,(
% 0.21/0.51    r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | ~spl3_71),
% 0.21/0.51    inference(avatar_component_clause,[],[f720])).
% 0.21/0.51  fof(f723,plain,(
% 0.21/0.51    spl3_71 | ~spl3_32),
% 0.21/0.51    inference(avatar_split_clause,[],[f718,f329,f720])).
% 0.21/0.51  fof(f329,plain,(
% 0.21/0.51    spl3_32 <=> m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.51  fof(f718,plain,(
% 0.21/0.51    r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | ~spl3_32),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f714])).
% 0.21/0.51  fof(f714,plain,(
% 0.21/0.51    r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | ~spl3_32),
% 0.21/0.51    inference(resolution,[],[f398,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.51  fof(f398,plain,(
% 0.21/0.51    ( ! [X2] : (r2_hidden(sK2(k5_xboole_0(k2_struct_0(sK0),sK1),X2),k2_struct_0(sK0)) | r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),X2)) ) | ~spl3_32),
% 0.21/0.51    inference(resolution,[],[f352,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f352,plain,(
% 0.21/0.51    ( ! [X3] : (~r2_hidden(X3,k5_xboole_0(k2_struct_0(sK0),sK1)) | r2_hidden(X3,k2_struct_0(sK0))) ) | ~spl3_32),
% 0.21/0.51    inference(resolution,[],[f331,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.51  fof(f331,plain,(
% 0.21/0.51    m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f329])).
% 0.21/0.51  fof(f578,plain,(
% 0.21/0.51    spl3_55 | ~spl3_32 | ~spl3_43),
% 0.21/0.51    inference(avatar_split_clause,[],[f566,f422,f329,f573])).
% 0.21/0.51  fof(f422,plain,(
% 0.21/0.51    spl3_43 <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.51  fof(f566,plain,(
% 0.21/0.51    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) | (~spl3_32 | ~spl3_43)),
% 0.21/0.51    inference(superposition,[],[f424,f340])).
% 0.21/0.51  fof(f340,plain,(
% 0.21/0.51    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,k5_xboole_0(k2_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X0,k5_xboole_0(k2_struct_0(sK0),sK1)))) ) | ~spl3_32),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f331,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f60,f50])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.51  fof(f424,plain,(
% 0.21/0.51    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)) | ~spl3_43),
% 0.21/0.51    inference(avatar_component_clause,[],[f422])).
% 0.21/0.51  fof(f430,plain,(
% 0.21/0.51    spl3_43 | ~spl3_18 | ~spl3_31),
% 0.21/0.51    inference(avatar_split_clause,[],[f429,f320,f214,f422])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    spl3_18 <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.51  fof(f320,plain,(
% 0.21/0.51    spl3_31 <=> k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.51  fof(f429,plain,(
% 0.21/0.51    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)) | (~spl3_18 | ~spl3_31)),
% 0.21/0.51    inference(forward_demodulation,[],[f216,f322])).
% 0.21/0.51  fof(f322,plain,(
% 0.21/0.51    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) | ~spl3_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f320])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl3_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f214])).
% 0.21/0.51  fof(f339,plain,(
% 0.21/0.51    spl3_32 | ~spl3_14 | ~spl3_31),
% 0.21/0.51    inference(avatar_split_clause,[],[f338,f320,f174,f329])).
% 0.21/0.51  fof(f338,plain,(
% 0.21/0.51    m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_14 | ~spl3_31)),
% 0.21/0.51    inference(subsumption_resolution,[],[f327,f176])).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_31),
% 0.21/0.51    inference(superposition,[],[f54,f322])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.51  fof(f337,plain,(
% 0.21/0.51    ~spl3_33 | spl3_13 | ~spl3_31),
% 0.21/0.51    inference(avatar_split_clause,[],[f325,f320,f169,f334])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    spl3_13 <=> v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.51  fof(f325,plain,(
% 0.21/0.51    ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | (spl3_13 | ~spl3_31)),
% 0.21/0.51    inference(backward_demodulation,[],[f170,f322])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | spl3_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f169])).
% 0.21/0.51  fof(f323,plain,(
% 0.21/0.51    spl3_31 | ~spl3_6 | ~spl3_8 | ~spl3_29),
% 0.21/0.51    inference(avatar_split_clause,[],[f318,f305,f129,f99,f320])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl3_8 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    spl3_29 <=> sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.51  fof(f318,plain,(
% 0.21/0.51    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) | (~spl3_6 | ~spl3_8 | ~spl3_29)),
% 0.21/0.51    inference(forward_demodulation,[],[f317,f307])).
% 0.21/0.51  fof(f307,plain,(
% 0.21/0.51    sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) | ~spl3_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f305])).
% 0.21/0.51  fof(f317,plain,(
% 0.21/0.51    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) | (~spl3_6 | ~spl3_8)),
% 0.21/0.51    inference(forward_demodulation,[],[f131,f101])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) | ~spl3_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f129])).
% 0.21/0.51  fof(f309,plain,(
% 0.21/0.51    spl3_29 | ~spl3_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f303,f297,f305])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    spl3_28 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.51  fof(f303,plain,(
% 0.21/0.51    sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) | ~spl3_28),
% 0.21/0.51    inference(resolution,[],[f299,f63])).
% 0.21/0.51  fof(f299,plain,(
% 0.21/0.51    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl3_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f297])).
% 0.21/0.51  fof(f300,plain,(
% 0.21/0.51    spl3_28 | ~spl3_3 | ~spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f295,f99,f77,f297])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f295,plain,(
% 0.21/0.51    r1_tarski(sK1,k2_struct_0(sK0)) | (~spl3_3 | ~spl3_6)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f293])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    r1_tarski(sK1,k2_struct_0(sK0)) | r1_tarski(sK1,k2_struct_0(sK0)) | (~spl3_3 | ~spl3_6)),
% 0.21/0.51    inference(resolution,[],[f228,f59])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    ( ! [X2] : (r2_hidden(sK2(sK1,X2),k2_struct_0(sK0)) | r1_tarski(sK1,X2)) ) | (~spl3_3 | ~spl3_6)),
% 0.21/0.51    inference(resolution,[],[f161,f58])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(X3,k2_struct_0(sK0))) ) | (~spl3_3 | ~spl3_6)),
% 0.21/0.51    inference(backward_demodulation,[],[f118,f101])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(X3,u1_struct_0(sK0))) ) | ~spl3_3),
% 0.21/0.51    inference(resolution,[],[f79,f56])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f77])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    spl3_18 | ~spl3_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f212,f174,f214])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl3_14),
% 0.21/0.51    inference(forward_demodulation,[],[f186,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    k7_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0)),sK1) = k9_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0)),k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl3_14),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f44,f176,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    ~spl3_13 | spl3_2 | ~spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f180,f99,f71,f169])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl3_2 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | (spl3_2 | ~spl3_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f73,f101])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f71])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    spl3_14 | ~spl3_3 | ~spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f163,f99,f77,f174])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_3 | ~spl3_6)),
% 0.21/0.51    inference(backward_demodulation,[],[f79,f101])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    spl3_8 | ~spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f156,f77,f129])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) | ~spl3_3),
% 0.21/0.51    inference(forward_demodulation,[],[f119,f49])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) | ~spl3_3),
% 0.21/0.51    inference(resolution,[],[f79,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f55,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f51,f50])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ~spl3_12 | spl3_1 | ~spl3_3 | ~spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f105,f82,f77,f67,f152])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    spl3_12 <=> v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | (spl3_1 | ~spl3_3 | ~spl3_4)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f84,f69,f79,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ~v4_pre_topc(sK1,sK0) | spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f67])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl3_6 | ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f97,f91,f99])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl3_5 <=> l1_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.21/0.51    inference(resolution,[],[f93,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    l1_struct_0(sK0) | ~spl3_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f91])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl3_5 | ~spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f89,f82,f91])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    l1_struct_0(sK0) | ~spl3_4),
% 0.21/0.51    inference(resolution,[],[f84,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f39,f82])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.52    inference(negated_conjecture,[],[f17])).
% 0.21/0.52  fof(f17,conjecture,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f40,f77])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl3_1 | spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f41,f71,f67])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f42,f71,f67])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (21598)------------------------------
% 0.21/0.52  % (21598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21598)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (21598)Memory used [KB]: 7036
% 0.21/0.52  % (21598)Time elapsed: 0.092 s
% 0.21/0.52  % (21598)------------------------------
% 0.21/0.52  % (21598)------------------------------
% 0.21/0.52  % (21572)Success in time 0.157 s
%------------------------------------------------------------------------------
