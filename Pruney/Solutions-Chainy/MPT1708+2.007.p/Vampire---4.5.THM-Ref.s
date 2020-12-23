%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:48 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 392 expanded)
%              Number of leaves         :   40 ( 164 expanded)
%              Depth                    :   15
%              Number of atoms          :  717 (2785 expanded)
%              Number of equality atoms :   80 ( 461 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f496,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f107,f133,f136,f139,f142,f152,f196,f198,f201,f208,f210,f235,f240,f341,f456,f480,f494])).

fof(f494,plain,
    ( spl4_19
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f488])).

fof(f488,plain,
    ( $false
    | spl4_19
    | ~ spl4_33 ),
    inference(resolution,[],[f462,f253])).

fof(f253,plain,
    ( ~ m1_subset_1(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl4_19 ),
    inference(resolution,[],[f239,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f239,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl4_19
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f462,plain,
    ( m1_subset_1(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl4_33 ),
    inference(superposition,[],[f188,f455])).

fof(f455,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f453])).

fof(f453,plain,
    ( spl4_33
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f188,plain,(
    ! [X0,X1] : m1_subset_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_zfmisc_1(X1)) ),
    inference(resolution,[],[f168,f98])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f54,f53])).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f67,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f68,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f72,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f73,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

% (20649)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (20657)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f72,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f480,plain,
    ( spl4_18
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | spl4_18
    | ~ spl4_33 ),
    inference(resolution,[],[f464,f234])).

fof(f234,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl4_18
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f464,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl4_33 ),
    inference(superposition,[],[f84,f455])).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f61,f81])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f456,plain,
    ( spl4_33
    | ~ spl4_11
    | ~ spl4_10
    | ~ spl4_8
    | ~ spl4_6
    | spl4_5
    | spl4_3
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f446,f339,f101,f110,f114,f122,f130,f146,f453])).

fof(f146,plain,
    ( spl4_11
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f130,plain,
    ( spl4_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f122,plain,
    ( spl4_8
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f114,plain,
    ( spl4_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f110,plain,
    ( spl4_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f101,plain,
    ( spl4_3
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f339,plain,
    ( spl4_31
  <=> ! [X0] :
        ( u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2)))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(k2_tsep_1(X0,sK1,sK2),X0)
        | v2_struct_0(k2_tsep_1(X0,sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f446,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2)))
    | spl4_3
    | ~ spl4_31 ),
    inference(resolution,[],[f340,f102])).

fof(f102,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f340,plain,
    ( ! [X0] :
        ( v2_struct_0(k2_tsep_1(X0,sK1,sK2))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(k2_tsep_1(X0,sK1,sK2),X0)
        | u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2))) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f339])).

fof(f341,plain,
    ( spl4_7
    | spl4_9
    | spl4_31 ),
    inference(avatar_split_clause,[],[f337,f339,f126,f118])).

fof(f118,plain,
    ( spl4_7
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f126,plain,
    ( spl4_9
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f337,plain,(
    ! [X0] :
      ( u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2)))
      | v2_struct_0(k2_tsep_1(X0,sK1,sK2))
      | ~ m1_pre_topc(k2_tsep_1(X0,sK1,sK2),X0)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f263,f50])).

fof(f50,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ! [X4] :
          ( sK3 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      | ! [X5] :
          ( sK3 != X5
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
    & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f38,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( X3 != X4
                          | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                      | ! [X5] :
                          ( X3 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                    & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  | ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2))) )
            & ~ r1_tsep_1(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                | ! [X5] :
                    ( X3 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
              & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2))) )
          & ~ r1_tsep_1(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              | ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
            & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2))) )
        & ~ r1_tsep_1(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
            | ! [X5] :
                ( X3 != X5
                | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
          & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) )
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
          | ! [X5] :
              ( X3 != X5
              | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
        & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) )
   => ( ( ! [X4] :
            ( sK3 != X4
            | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
        | ! [X5] :
            ( sK3 != X5
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
      & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                   => ( ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) )
                      & ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tmap_1)).

fof(f263,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f262])).

fof(f262,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f88,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f57,f81])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f240,plain,
    ( spl4_9
    | ~ spl4_10
    | ~ spl4_19
    | spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f228,f150,f94,f237,f130,f126])).

fof(f94,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f150,plain,
    ( spl4_12
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))
        | m1_subset_1(sK3,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f228,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | spl4_2
    | ~ spl4_12 ),
    inference(resolution,[],[f226,f96])).

fof(f96,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f226,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,u1_struct_0(X0))
        | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))
        | m1_subset_1(sK3,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_12 ),
    inference(resolution,[],[f223,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))
        | m1_subset_1(sK3,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0) )
    | ~ spl4_12 ),
    inference(resolution,[],[f151,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f151,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))
        | m1_subset_1(sK3,u1_struct_0(X0)) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f150])).

fof(f235,plain,
    ( spl4_7
    | ~ spl4_8
    | ~ spl4_18
    | spl4_1
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f227,f150,f90,f232,f122,f118])).

fof(f90,plain,
    ( spl4_1
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f227,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | spl4_1
    | ~ spl4_12 ),
    inference(resolution,[],[f226,f92])).

fof(f92,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f210,plain,(
    ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl4_9 ),
    inference(resolution,[],[f128,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f128,plain,
    ( v2_struct_0(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f208,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl4_7 ),
    inference(resolution,[],[f120,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f120,plain,
    ( v2_struct_0(sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f201,plain,
    ( spl4_9
    | spl4_7
    | ~ spl4_10
    | ~ spl4_8
    | spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f199,f194,f146,f122,f130,f118,f126])).

fof(f194,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f199,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | spl4_11
    | ~ spl4_15 ),
    inference(resolution,[],[f195,f148])).

fof(f148,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f194])).

fof(f198,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl4_5 ),
    inference(resolution,[],[f112,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f112,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f196,plain,
    ( spl4_5
    | spl4_15 ),
    inference(avatar_split_clause,[],[f191,f194,f110])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f71,f45])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f152,plain,
    ( ~ spl4_6
    | ~ spl4_11
    | spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f144,f105,f150,f146,f114])).

fof(f105,plain,
    ( spl4_4
  <=> ! [X0] :
        ( m1_subset_1(sK3,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | m1_subset_1(sK3,u1_struct_0(X0))
        | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f143,f44])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | m1_subset_1(sK3,u1_struct_0(X0))
        | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f106,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f106,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | m1_subset_1(sK3,u1_struct_0(X0)) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f142,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f132,f49])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f132,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f139,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl4_8 ),
    inference(resolution,[],[f124,f47])).

fof(f47,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f124,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f136,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl4_6 ),
    inference(resolution,[],[f116,f45])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f114])).

fof(f133,plain,
    ( spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_8
    | spl4_9
    | ~ spl4_10
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f108,f101,f130,f126,f122,f118,f114,f110])).

fof(f108,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f69,f103])).

fof(f103,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f107,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f99,f105,f101])).

fof(f99,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f56,f51])).

fof(f51,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f97,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f87,f94,f90])).

fof(f87,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | sK3 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X5] :
      ( sK3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:37:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.21/0.52  % (20640)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.21/0.53  % (20651)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.21/0.53  % (20643)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.21/0.54  % (20635)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.54  % (20641)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.54  % (20636)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.54  % (20659)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.54  % (20658)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.54  % (20645)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.54  % (20663)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.54  % (20639)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.41/0.54  % (20645)Refutation not found, incomplete strategy% (20645)------------------------------
% 1.41/0.54  % (20645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (20645)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (20645)Memory used [KB]: 10746
% 1.41/0.54  % (20645)Time elapsed: 0.123 s
% 1.41/0.54  % (20645)------------------------------
% 1.41/0.54  % (20645)------------------------------
% 1.41/0.55  % (20646)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (20646)Refutation not found, incomplete strategy% (20646)------------------------------
% 1.41/0.55  % (20646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (20660)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.55  % (20638)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.55  % (20664)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.55  % (20650)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.55  % (20655)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (20662)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (20652)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.55  % (20661)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.55  % (20646)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (20646)Memory used [KB]: 10746
% 1.41/0.55  % (20646)Time elapsed: 0.125 s
% 1.41/0.55  % (20646)------------------------------
% 1.41/0.55  % (20646)------------------------------
% 1.41/0.55  % (20656)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.56  % (20653)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.56  % (20647)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.56  % (20644)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.56  % (20642)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.56  % (20654)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.56  % (20648)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.56  % (20637)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.59  % (20647)Refutation found. Thanks to Tanya!
% 1.41/0.59  % SZS status Theorem for theBenchmark
% 1.41/0.59  % SZS output start Proof for theBenchmark
% 1.41/0.59  fof(f496,plain,(
% 1.41/0.59    $false),
% 1.41/0.59    inference(avatar_sat_refutation,[],[f97,f107,f133,f136,f139,f142,f152,f196,f198,f201,f208,f210,f235,f240,f341,f456,f480,f494])).
% 1.41/0.59  fof(f494,plain,(
% 1.41/0.59    spl4_19 | ~spl4_33),
% 1.41/0.59    inference(avatar_contradiction_clause,[],[f488])).
% 1.41/0.59  fof(f488,plain,(
% 1.41/0.59    $false | (spl4_19 | ~spl4_33)),
% 1.41/0.59    inference(resolution,[],[f462,f253])).
% 1.41/0.59  fof(f253,plain,(
% 1.41/0.59    ~m1_subset_1(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | spl4_19),
% 1.41/0.59    inference(resolution,[],[f239,f64])).
% 1.41/0.59  fof(f64,plain,(
% 1.41/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.41/0.59    inference(cnf_transformation,[],[f42])).
% 1.41/0.59  fof(f42,plain,(
% 1.41/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.41/0.59    inference(nnf_transformation,[],[f13])).
% 1.41/0.59  fof(f13,axiom,(
% 1.41/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.41/0.59  fof(f239,plain,(
% 1.41/0.59    ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) | spl4_19),
% 1.41/0.59    inference(avatar_component_clause,[],[f237])).
% 1.41/0.59  fof(f237,plain,(
% 1.41/0.59    spl4_19 <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2))),
% 1.41/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.41/0.59  fof(f462,plain,(
% 1.41/0.59    m1_subset_1(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl4_33),
% 1.41/0.59    inference(superposition,[],[f188,f455])).
% 1.41/0.59  fof(f455,plain,(
% 1.41/0.59    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl4_33),
% 1.41/0.59    inference(avatar_component_clause,[],[f453])).
% 1.41/0.59  fof(f453,plain,(
% 1.41/0.59    spl4_33 <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2)))),
% 1.41/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.41/0.59  fof(f188,plain,(
% 1.41/0.59    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_zfmisc_1(X1))) )),
% 1.41/0.59    inference(resolution,[],[f168,f98])).
% 1.41/0.59  fof(f98,plain,(
% 1.41/0.59    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.41/0.59    inference(forward_demodulation,[],[f54,f53])).
% 1.41/0.59  fof(f53,plain,(
% 1.41/0.59    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.41/0.59    inference(cnf_transformation,[],[f8])).
% 1.41/0.59  fof(f8,axiom,(
% 1.41/0.59    ! [X0] : k2_subset_1(X0) = X0),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.41/0.59  fof(f54,plain,(
% 1.41/0.59    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.41/0.59    inference(cnf_transformation,[],[f9])).
% 1.41/0.59  fof(f9,axiom,(
% 1.41/0.59    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.41/0.59  fof(f168,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X0))) )),
% 1.41/0.59    inference(duplicate_literal_removal,[],[f166])).
% 1.41/0.59  fof(f166,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.41/0.59    inference(superposition,[],[f67,f85])).
% 1.41/0.59  fof(f85,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.41/0.59    inference(definition_unfolding,[],[f68,f81])).
% 1.41/0.59  fof(f81,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.41/0.59    inference(definition_unfolding,[],[f62,f80])).
% 1.41/0.59  fof(f80,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.41/0.59    inference(definition_unfolding,[],[f63,f79])).
% 1.41/0.59  fof(f79,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.41/0.59    inference(definition_unfolding,[],[f66,f78])).
% 1.41/0.59  fof(f78,plain,(
% 1.41/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.41/0.59    inference(definition_unfolding,[],[f72,f77])).
% 1.41/0.59  fof(f77,plain,(
% 1.41/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.41/0.59    inference(definition_unfolding,[],[f73,f76])).
% 1.41/0.59  fof(f76,plain,(
% 1.41/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.41/0.59    inference(definition_unfolding,[],[f74,f75])).
% 1.41/0.59  fof(f75,plain,(
% 1.41/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f7])).
% 1.41/0.59  fof(f7,axiom,(
% 1.41/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.41/0.59  fof(f74,plain,(
% 1.41/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f6])).
% 1.41/0.59  fof(f6,axiom,(
% 1.41/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.41/0.59  fof(f73,plain,(
% 1.41/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f5])).
% 1.41/0.59  fof(f5,axiom,(
% 1.41/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.41/0.59  % (20649)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.41/0.60  % (20657)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.61  fof(f72,plain,(
% 1.41/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f4])).
% 1.41/0.61  fof(f4,axiom,(
% 1.41/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.41/0.61  fof(f66,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f3])).
% 1.41/0.61  fof(f3,axiom,(
% 1.41/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.41/0.61  fof(f63,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f2])).
% 1.41/0.61  fof(f2,axiom,(
% 1.41/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.61  fof(f62,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.41/0.61    inference(cnf_transformation,[],[f12])).
% 1.41/0.61  fof(f12,axiom,(
% 1.41/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.41/0.61  fof(f68,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.41/0.61    inference(cnf_transformation,[],[f32])).
% 1.41/0.61  fof(f32,plain,(
% 1.41/0.61    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.41/0.61    inference(ennf_transformation,[],[f11])).
% 1.41/0.61  fof(f11,axiom,(
% 1.41/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.41/0.61  fof(f67,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.41/0.61    inference(cnf_transformation,[],[f31])).
% 1.41/0.61  fof(f31,plain,(
% 1.41/0.61    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.41/0.61    inference(ennf_transformation,[],[f10])).
% 1.41/0.61  fof(f10,axiom,(
% 1.41/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 1.41/0.61  fof(f480,plain,(
% 1.41/0.61    spl4_18 | ~spl4_33),
% 1.41/0.61    inference(avatar_contradiction_clause,[],[f475])).
% 1.41/0.61  fof(f475,plain,(
% 1.41/0.61    $false | (spl4_18 | ~spl4_33)),
% 1.41/0.61    inference(resolution,[],[f464,f234])).
% 1.41/0.61  fof(f234,plain,(
% 1.41/0.61    ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1)) | spl4_18),
% 1.41/0.61    inference(avatar_component_clause,[],[f232])).
% 1.41/0.61  fof(f232,plain,(
% 1.41/0.61    spl4_18 <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.41/0.61  fof(f464,plain,(
% 1.41/0.61    r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1)) | ~spl4_33),
% 1.41/0.61    inference(superposition,[],[f84,f455])).
% 1.41/0.61  fof(f84,plain,(
% 1.41/0.61    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 1.41/0.61    inference(definition_unfolding,[],[f61,f81])).
% 1.41/0.61  fof(f61,plain,(
% 1.41/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f1])).
% 1.41/0.61  fof(f1,axiom,(
% 1.41/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.41/0.61  fof(f456,plain,(
% 1.41/0.61    spl4_33 | ~spl4_11 | ~spl4_10 | ~spl4_8 | ~spl4_6 | spl4_5 | spl4_3 | ~spl4_31),
% 1.41/0.61    inference(avatar_split_clause,[],[f446,f339,f101,f110,f114,f122,f130,f146,f453])).
% 1.41/0.61  fof(f146,plain,(
% 1.41/0.61    spl4_11 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.41/0.61  fof(f130,plain,(
% 1.41/0.61    spl4_10 <=> m1_pre_topc(sK2,sK0)),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.41/0.61  fof(f122,plain,(
% 1.41/0.61    spl4_8 <=> m1_pre_topc(sK1,sK0)),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.41/0.61  fof(f114,plain,(
% 1.41/0.61    spl4_6 <=> l1_pre_topc(sK0)),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.41/0.61  fof(f110,plain,(
% 1.41/0.61    spl4_5 <=> v2_struct_0(sK0)),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.41/0.61  fof(f101,plain,(
% 1.41/0.61    spl4_3 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.41/0.61  fof(f339,plain,(
% 1.41/0.61    spl4_31 <=> ! [X0] : (u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(k2_tsep_1(X0,sK1,sK2),X0) | v2_struct_0(k2_tsep_1(X0,sK1,sK2)))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.41/0.61  fof(f446,plain,(
% 1.41/0.61    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2))) | (spl4_3 | ~spl4_31)),
% 1.41/0.61    inference(resolution,[],[f340,f102])).
% 1.41/0.61  fof(f102,plain,(
% 1.41/0.61    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | spl4_3),
% 1.41/0.61    inference(avatar_component_clause,[],[f101])).
% 1.41/0.61  fof(f340,plain,(
% 1.41/0.61    ( ! [X0] : (v2_struct_0(k2_tsep_1(X0,sK1,sK2)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(k2_tsep_1(X0,sK1,sK2),X0) | u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2)))) ) | ~spl4_31),
% 1.41/0.61    inference(avatar_component_clause,[],[f339])).
% 1.41/0.61  fof(f341,plain,(
% 1.41/0.61    spl4_7 | spl4_9 | spl4_31),
% 1.41/0.61    inference(avatar_split_clause,[],[f337,f339,f126,f118])).
% 1.41/0.61  fof(f118,plain,(
% 1.41/0.61    spl4_7 <=> v2_struct_0(sK1)),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.41/0.61  fof(f126,plain,(
% 1.41/0.61    spl4_9 <=> v2_struct_0(sK2)),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.41/0.61  fof(f337,plain,(
% 1.41/0.61    ( ! [X0] : (u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k2_tsep_1(X0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(X0,sK1,sK2),X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.61    inference(resolution,[],[f263,f50])).
% 1.41/0.61  fof(f50,plain,(
% 1.41/0.61    ~r1_tsep_1(sK1,sK2)),
% 1.41/0.61    inference(cnf_transformation,[],[f39])).
% 1.41/0.61  fof(f39,plain,(
% 1.41/0.61    ((((! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.41/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f38,f37,f36,f35])).
% 1.41/0.61  fof(f35,plain,(
% 1.41/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.41/0.61    introduced(choice_axiom,[])).
% 1.41/0.61  fof(f36,plain,(
% 1.41/0.61    ? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2)))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.41/0.61    introduced(choice_axiom,[])).
% 1.41/0.61  fof(f37,plain,(
% 1.41/0.61    ? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2)))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.41/0.61    introduced(choice_axiom,[])).
% 1.41/0.61  fof(f38,plain,(
% 1.41/0.61    ? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) => ((! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))))),
% 1.41/0.61    introduced(choice_axiom,[])).
% 1.41/0.61  fof(f23,plain,(
% 1.41/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.41/0.61    inference(flattening,[],[f22])).
% 1.41/0.61  fof(f22,plain,(
% 1.41/0.61    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.41/0.61    inference(ennf_transformation,[],[f21])).
% 1.41/0.61  fof(f21,plain,(
% 1.41/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 1.41/0.61    inference(rectify,[],[f20])).
% 1.41/0.61  fof(f20,negated_conjecture,(
% 1.41/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.41/0.61    inference(negated_conjecture,[],[f19])).
% 1.41/0.61  fof(f19,conjecture,(
% 1.41/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tmap_1)).
% 1.41/0.61  fof(f263,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.61    inference(duplicate_literal_removal,[],[f262])).
% 1.41/0.61  fof(f262,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.61    inference(resolution,[],[f88,f70])).
% 1.41/0.61  fof(f70,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f34])).
% 1.41/0.61  fof(f34,plain,(
% 1.41/0.61    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.41/0.61    inference(flattening,[],[f33])).
% 1.41/0.61  fof(f33,plain,(
% 1.41/0.61    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.41/0.61    inference(ennf_transformation,[],[f17])).
% 1.41/0.61  fof(f17,axiom,(
% 1.41/0.61    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 1.41/0.61  fof(f88,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.61    inference(equality_resolution,[],[f83])).
% 1.41/0.61  fof(f83,plain,(
% 1.41/0.61    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.61    inference(definition_unfolding,[],[f57,f81])).
% 1.41/0.61  fof(f57,plain,(
% 1.41/0.61    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f40])).
% 1.41/0.61  fof(f40,plain,(
% 1.41/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.41/0.61    inference(nnf_transformation,[],[f28])).
% 1.41/0.61  fof(f28,plain,(
% 1.41/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.41/0.61    inference(flattening,[],[f27])).
% 1.41/0.61  fof(f27,plain,(
% 1.41/0.61    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.41/0.61    inference(ennf_transformation,[],[f16])).
% 1.41/0.61  fof(f16,axiom,(
% 1.41/0.61    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).
% 1.41/0.61  fof(f240,plain,(
% 1.41/0.61    spl4_9 | ~spl4_10 | ~spl4_19 | spl4_2 | ~spl4_12),
% 1.41/0.61    inference(avatar_split_clause,[],[f228,f150,f94,f237,f130,f126])).
% 1.41/0.61  fof(f94,plain,(
% 1.41/0.61    spl4_2 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.41/0.61  fof(f150,plain,(
% 1.41/0.61    spl4_12 <=> ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) | m1_subset_1(sK3,u1_struct_0(X0)))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.41/0.61  fof(f228,plain,(
% 1.41/0.61    ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (spl4_2 | ~spl4_12)),
% 1.41/0.61    inference(resolution,[],[f226,f96])).
% 1.41/0.61  fof(f96,plain,(
% 1.41/0.61    ~m1_subset_1(sK3,u1_struct_0(sK2)) | spl4_2),
% 1.41/0.61    inference(avatar_component_clause,[],[f94])).
% 1.41/0.61  fof(f226,plain,(
% 1.41/0.61    ( ! [X0] : (m1_subset_1(sK3,u1_struct_0(X0)) | ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | ~spl4_12),
% 1.41/0.61    inference(duplicate_literal_removal,[],[f224])).
% 1.41/0.61  fof(f224,plain,(
% 1.41/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) | m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | ~spl4_12),
% 1.41/0.61    inference(resolution,[],[f223,f45])).
% 1.41/0.61  fof(f45,plain,(
% 1.41/0.61    l1_pre_topc(sK0)),
% 1.41/0.61    inference(cnf_transformation,[],[f39])).
% 1.41/0.61  fof(f223,plain,(
% 1.41/0.61    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,sK0) | ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) | m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0)) ) | ~spl4_12),
% 1.41/0.61    inference(resolution,[],[f151,f55])).
% 1.41/0.61  fof(f55,plain,(
% 1.41/0.61    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f24])).
% 1.41/0.61  fof(f24,plain,(
% 1.41/0.61    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.41/0.61    inference(ennf_transformation,[],[f14])).
% 1.41/0.61  fof(f14,axiom,(
% 1.41/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.41/0.61  fof(f151,plain,(
% 1.41/0.61    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) | m1_subset_1(sK3,u1_struct_0(X0))) ) | ~spl4_12),
% 1.41/0.61    inference(avatar_component_clause,[],[f150])).
% 1.41/0.61  fof(f235,plain,(
% 1.41/0.61    spl4_7 | ~spl4_8 | ~spl4_18 | spl4_1 | ~spl4_12),
% 1.41/0.61    inference(avatar_split_clause,[],[f227,f150,f90,f232,f122,f118])).
% 1.41/0.61  fof(f90,plain,(
% 1.41/0.61    spl4_1 <=> m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.41/0.61  fof(f227,plain,(
% 1.41/0.61    ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | (spl4_1 | ~spl4_12)),
% 1.41/0.61    inference(resolution,[],[f226,f92])).
% 1.41/0.61  fof(f92,plain,(
% 1.41/0.61    ~m1_subset_1(sK3,u1_struct_0(sK1)) | spl4_1),
% 1.41/0.61    inference(avatar_component_clause,[],[f90])).
% 1.41/0.61  fof(f210,plain,(
% 1.41/0.61    ~spl4_9),
% 1.41/0.61    inference(avatar_contradiction_clause,[],[f209])).
% 1.41/0.61  fof(f209,plain,(
% 1.41/0.61    $false | ~spl4_9),
% 1.41/0.61    inference(resolution,[],[f128,f48])).
% 1.41/0.61  fof(f48,plain,(
% 1.41/0.61    ~v2_struct_0(sK2)),
% 1.41/0.61    inference(cnf_transformation,[],[f39])).
% 1.41/0.61  fof(f128,plain,(
% 1.41/0.61    v2_struct_0(sK2) | ~spl4_9),
% 1.41/0.61    inference(avatar_component_clause,[],[f126])).
% 1.41/0.61  fof(f208,plain,(
% 1.41/0.61    ~spl4_7),
% 1.41/0.61    inference(avatar_contradiction_clause,[],[f207])).
% 1.41/0.61  fof(f207,plain,(
% 1.41/0.61    $false | ~spl4_7),
% 1.41/0.61    inference(resolution,[],[f120,f46])).
% 1.41/0.61  fof(f46,plain,(
% 1.41/0.61    ~v2_struct_0(sK1)),
% 1.41/0.61    inference(cnf_transformation,[],[f39])).
% 1.41/0.61  fof(f120,plain,(
% 1.41/0.61    v2_struct_0(sK1) | ~spl4_7),
% 1.41/0.61    inference(avatar_component_clause,[],[f118])).
% 1.41/0.61  fof(f201,plain,(
% 1.41/0.61    spl4_9 | spl4_7 | ~spl4_10 | ~spl4_8 | spl4_11 | ~spl4_15),
% 1.41/0.61    inference(avatar_split_clause,[],[f199,f194,f146,f122,f130,f118,f126])).
% 1.41/0.61  fof(f194,plain,(
% 1.41/0.61    spl4_15 <=> ! [X1,X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0) | v2_struct_0(X1) | v2_struct_0(X0))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.41/0.61  fof(f199,plain,(
% 1.41/0.61    ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | v2_struct_0(sK2) | (spl4_11 | ~spl4_15)),
% 1.41/0.61    inference(resolution,[],[f195,f148])).
% 1.41/0.61  fof(f148,plain,(
% 1.41/0.61    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | spl4_11),
% 1.41/0.61    inference(avatar_component_clause,[],[f146])).
% 1.41/0.61  fof(f195,plain,(
% 1.41/0.61    ( ! [X0,X1] : (m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | v2_struct_0(X0)) ) | ~spl4_15),
% 1.41/0.61    inference(avatar_component_clause,[],[f194])).
% 1.41/0.61  fof(f198,plain,(
% 1.41/0.61    ~spl4_5),
% 1.41/0.61    inference(avatar_contradiction_clause,[],[f197])).
% 1.41/0.61  fof(f197,plain,(
% 1.41/0.61    $false | ~spl4_5),
% 1.41/0.61    inference(resolution,[],[f112,f43])).
% 1.41/0.61  fof(f43,plain,(
% 1.41/0.61    ~v2_struct_0(sK0)),
% 1.41/0.61    inference(cnf_transformation,[],[f39])).
% 1.41/0.61  fof(f112,plain,(
% 1.41/0.61    v2_struct_0(sK0) | ~spl4_5),
% 1.41/0.61    inference(avatar_component_clause,[],[f110])).
% 1.41/0.61  fof(f196,plain,(
% 1.41/0.61    spl4_5 | spl4_15),
% 1.41/0.61    inference(avatar_split_clause,[],[f191,f194,f110])).
% 1.41/0.61  fof(f191,plain,(
% 1.41/0.61    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0) | v2_struct_0(sK0)) )),
% 1.41/0.61    inference(resolution,[],[f71,f45])).
% 1.41/0.61  fof(f71,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | v2_struct_0(X0)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f34])).
% 1.41/0.61  fof(f152,plain,(
% 1.41/0.61    ~spl4_6 | ~spl4_11 | spl4_12 | ~spl4_4),
% 1.41/0.61    inference(avatar_split_clause,[],[f144,f105,f150,f146,f114])).
% 1.41/0.61  fof(f105,plain,(
% 1.41/0.61    spl4_4 <=> ! [X0] : (m1_subset_1(sK3,u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.41/0.61  fof(f144,plain,(
% 1.41/0.61    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(sK3,u1_struct_0(X0)) | ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0)) ) | ~spl4_4),
% 1.41/0.61    inference(resolution,[],[f143,f44])).
% 1.41/0.61  fof(f44,plain,(
% 1.41/0.61    v2_pre_topc(sK0)),
% 1.41/0.61    inference(cnf_transformation,[],[f39])).
% 1.41/0.61  fof(f143,plain,(
% 1.41/0.61    ( ! [X0,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK3,u1_struct_0(X0)) | ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1) | ~l1_pre_topc(X1) | v2_struct_0(X0)) ) | ~spl4_4),
% 1.41/0.61    inference(resolution,[],[f106,f59])).
% 1.41/0.61  fof(f59,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f41])).
% 1.41/0.61  fof(f41,plain,(
% 1.41/0.61    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.41/0.61    inference(nnf_transformation,[],[f30])).
% 1.41/0.61  fof(f30,plain,(
% 1.41/0.61    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.41/0.61    inference(flattening,[],[f29])).
% 1.41/0.61  fof(f29,plain,(
% 1.41/0.61    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.41/0.61    inference(ennf_transformation,[],[f18])).
% 1.41/0.61  fof(f18,axiom,(
% 1.41/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 1.41/0.61  fof(f106,plain,(
% 1.41/0.61    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK3,u1_struct_0(X0))) ) | ~spl4_4),
% 1.41/0.61    inference(avatar_component_clause,[],[f105])).
% 1.41/0.61  fof(f142,plain,(
% 1.41/0.61    spl4_10),
% 1.41/0.61    inference(avatar_contradiction_clause,[],[f140])).
% 1.41/0.61  fof(f140,plain,(
% 1.41/0.61    $false | spl4_10),
% 1.41/0.61    inference(resolution,[],[f132,f49])).
% 1.41/0.61  fof(f49,plain,(
% 1.41/0.61    m1_pre_topc(sK2,sK0)),
% 1.41/0.61    inference(cnf_transformation,[],[f39])).
% 1.41/0.61  fof(f132,plain,(
% 1.41/0.61    ~m1_pre_topc(sK2,sK0) | spl4_10),
% 1.41/0.61    inference(avatar_component_clause,[],[f130])).
% 1.41/0.61  fof(f139,plain,(
% 1.41/0.61    spl4_8),
% 1.41/0.61    inference(avatar_contradiction_clause,[],[f137])).
% 1.41/0.61  fof(f137,plain,(
% 1.41/0.61    $false | spl4_8),
% 1.41/0.61    inference(resolution,[],[f124,f47])).
% 1.41/0.61  fof(f47,plain,(
% 1.41/0.61    m1_pre_topc(sK1,sK0)),
% 1.41/0.61    inference(cnf_transformation,[],[f39])).
% 1.41/0.61  fof(f124,plain,(
% 1.41/0.61    ~m1_pre_topc(sK1,sK0) | spl4_8),
% 1.41/0.61    inference(avatar_component_clause,[],[f122])).
% 1.41/0.61  fof(f136,plain,(
% 1.41/0.61    spl4_6),
% 1.41/0.61    inference(avatar_contradiction_clause,[],[f134])).
% 1.41/0.61  fof(f134,plain,(
% 1.41/0.61    $false | spl4_6),
% 1.41/0.61    inference(resolution,[],[f116,f45])).
% 1.41/0.61  fof(f116,plain,(
% 1.41/0.61    ~l1_pre_topc(sK0) | spl4_6),
% 1.41/0.61    inference(avatar_component_clause,[],[f114])).
% 1.41/0.61  fof(f133,plain,(
% 1.41/0.61    spl4_5 | ~spl4_6 | spl4_7 | ~spl4_8 | spl4_9 | ~spl4_10 | ~spl4_3),
% 1.41/0.61    inference(avatar_split_clause,[],[f108,f101,f130,f126,f122,f118,f114,f110])).
% 1.41/0.61  fof(f108,plain,(
% 1.41/0.61    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_3),
% 1.41/0.61    inference(resolution,[],[f69,f103])).
% 1.41/0.61  fof(f103,plain,(
% 1.41/0.61    v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl4_3),
% 1.41/0.61    inference(avatar_component_clause,[],[f101])).
% 1.41/0.61  fof(f69,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f34])).
% 1.41/0.61  fof(f107,plain,(
% 1.41/0.61    spl4_3 | spl4_4),
% 1.41/0.61    inference(avatar_split_clause,[],[f99,f105,f101])).
% 1.41/0.61  fof(f99,plain,(
% 1.41/0.61    ( ! [X0] : (m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.61    inference(resolution,[],[f56,f51])).
% 1.41/0.61  fof(f51,plain,(
% 1.41/0.61    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.41/0.61    inference(cnf_transformation,[],[f39])).
% 1.41/0.61  fof(f56,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f26])).
% 1.41/0.61  fof(f26,plain,(
% 1.41/0.61    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.41/0.61    inference(flattening,[],[f25])).
% 1.41/0.61  fof(f25,plain,(
% 1.41/0.61    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.41/0.61    inference(ennf_transformation,[],[f15])).
% 1.41/0.61  fof(f15,axiom,(
% 1.41/0.61    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.41/0.61  fof(f97,plain,(
% 1.41/0.61    ~spl4_1 | ~spl4_2),
% 1.41/0.61    inference(avatar_split_clause,[],[f87,f94,f90])).
% 1.41/0.61  fof(f87,plain,(
% 1.41/0.61    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.41/0.61    inference(equality_resolution,[],[f86])).
% 1.41/0.61  fof(f86,plain,(
% 1.41/0.61    ( ! [X5] : (~m1_subset_1(sK3,u1_struct_0(sK2)) | sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) )),
% 1.41/0.61    inference(equality_resolution,[],[f52])).
% 1.41/0.61  fof(f52,plain,(
% 1.41/0.61    ( ! [X4,X5] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) )),
% 1.41/0.61    inference(cnf_transformation,[],[f39])).
% 1.41/0.61  % SZS output end Proof for theBenchmark
% 1.41/0.61  % (20647)------------------------------
% 1.41/0.61  % (20647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.61  % (20647)Termination reason: Refutation
% 1.41/0.61  
% 1.41/0.61  % (20647)Memory used [KB]: 6652
% 1.41/0.61  % (20647)Time elapsed: 0.186 s
% 1.41/0.61  % (20647)------------------------------
% 1.41/0.61  % (20647)------------------------------
% 1.41/0.62  % (20634)Success in time 0.253 s
%------------------------------------------------------------------------------
