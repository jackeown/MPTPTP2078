%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:45 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 327 expanded)
%              Number of leaves         :   39 ( 137 expanded)
%              Depth                    :   13
%              Number of atoms          :  527 (1680 expanded)
%              Number of equality atoms :   67 ( 261 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f90,f94,f98,f102,f106,f114,f119,f125,f130,f209,f219,f222,f236,f252,f316,f328,f329,f330,f348])).

% (23859)Termination reason: Refutation not found, incomplete strategy

% (23859)Memory used [KB]: 6524
% (23859)Time elapsed: 0.161 s
% (23859)------------------------------
% (23859)------------------------------
fof(f348,plain,
    ( ~ spl7_23
    | spl7_1
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f341,f230,f84,f249])).

fof(f249,plain,
    ( spl7_23
  <=> r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f84,plain,
    ( spl7_1
  <=> v3_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f230,plain,
    ( spl7_19
  <=> v3_pre_topc(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f341,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2))
    | ~ spl7_19 ),
    inference(superposition,[],[f231,f160])).

fof(f160,plain,(
    ! [X8,X9] :
      ( k1_setfam_1(k2_tarski(X8,X9)) = X8
      | ~ r2_hidden(sK6(X8,X9,X8),X9) ) ),
    inference(global_subsumption,[],[f132,f155])).

fof(f155,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK6(X8,X9,X8),X9)
      | ~ r2_hidden(sK6(X8,X9,X8),X8)
      | k1_setfam_1(k2_tarski(X8,X9)) = X8 ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK6(X8,X9,X8),X9)
      | ~ r2_hidden(sK6(X8,X9,X8),X8)
      | k1_setfam_1(k2_tarski(X8,X9)) = X8
      | k1_setfam_1(k2_tarski(X8,X9)) = X8 ) ),
    inference(resolution,[],[f73,f132])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X2)
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f69,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f132,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1,X0),X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(factoring,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f67,f57])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f231,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),sK2)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f230])).

fof(f330,plain,
    ( sK3 != k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))
    | v3_pre_topc(sK3,sK2)
    | ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f329,plain,
    ( sK3 != k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))
    | u1_struct_0(sK2) != k2_struct_0(sK2)
    | m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f328,plain,
    ( spl7_27
    | spl7_26 ),
    inference(avatar_split_clause,[],[f319,f314,f324])).

fof(f324,plain,
    ( spl7_27
  <=> sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f314,plain,
    ( spl7_26
  <=> r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f319,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))
    | spl7_26 ),
    inference(resolution,[],[f315,f132])).

fof(f315,plain,
    ( ~ r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),sK3)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f314])).

fof(f316,plain,
    ( ~ spl7_26
    | ~ spl7_10
    | spl7_23 ),
    inference(avatar_split_clause,[],[f310,f249,f128,f314])).

fof(f128,plain,
    ( spl7_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f310,plain,
    ( ~ r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),sK3)
    | ~ spl7_10
    | spl7_23 ),
    inference(resolution,[],[f295,f129])).

fof(f129,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f295,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),X1) )
    | spl7_23 ),
    inference(resolution,[],[f267,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f267,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k2_struct_0(sK2))
        | ~ r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),X2) )
    | spl7_23 ),
    inference(resolution,[],[f250,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f250,plain,
    ( ~ r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2))
    | spl7_23 ),
    inference(avatar_component_clause,[],[f249])).

fof(f252,plain,
    ( ~ spl7_23
    | ~ spl7_10
    | spl7_20 ),
    inference(avatar_split_clause,[],[f242,f234,f128,f249])).

fof(f234,plain,
    ( spl7_20
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f242,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2))
    | spl7_20 ),
    inference(superposition,[],[f235,f160])).

fof(f235,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
    | spl7_20 ),
    inference(avatar_component_clause,[],[f234])).

fof(f236,plain,
    ( spl7_19
    | ~ spl7_8
    | ~ spl7_20
    | ~ spl7_3
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f227,f217,f92,f234,f117,f230])).

fof(f117,plain,
    ( spl7_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f92,plain,
    ( spl7_3
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f217,plain,
    ( spl7_17
  <=> ! [X0] :
        ( v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2)
        | ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f227,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),sK2)
    | ~ spl7_3
    | ~ spl7_17 ),
    inference(resolution,[],[f218,f93])).

fof(f93,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f217])).

fof(f222,plain,(
    spl7_16 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl7_16 ),
    inference(resolution,[],[f215,f107])).

fof(f107,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f49,f48])).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f215,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl7_16
  <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f219,plain,
    ( ~ spl7_16
    | spl7_17
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f211,f207,f217,f214])).

fof(f207,plain,
    ( spl7_15
  <=> ! [X0] :
        ( v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f211,plain,
    ( ! [X0] :
        ( v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) )
    | ~ spl7_15 ),
    inference(superposition,[],[f208,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f63,f57])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f208,plain,
    ( ! [X0] :
        ( v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f207])).

fof(f209,plain,
    ( ~ spl7_6
    | spl7_15
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f205,f123,f112,f96,f207,f104])).

fof(f104,plain,
    ( spl7_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f96,plain,
    ( spl7_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f112,plain,
    ( spl7_7
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f123,plain,
    ( spl7_9
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f205,plain,
    ( ! [X0] :
        ( v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f204,f124])).

fof(f124,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f203,f124])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f202,f113])).

fof(f113,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f79,f97])).

fof(f97,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v3_pre_topc(sK4(X0,X1,X2),X0)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).

fof(f130,plain,
    ( spl7_10
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f126,f123,f88,f128])).

fof(f88,plain,
    ( spl7_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f126,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(superposition,[],[f89,f124])).

fof(f89,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f125,plain,
    ( ~ spl7_6
    | spl7_9
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f120,f96,f123,f104])).

fof(f120,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(resolution,[],[f110,f97])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f108,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f108,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f50,f51])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f119,plain,
    ( spl7_8
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f115,f112,f100,f117])).

fof(f100,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f115,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(superposition,[],[f101,f113])).

fof(f101,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f114,plain,
    ( spl7_7
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f109,f104,f112])).

fof(f109,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl7_6 ),
    inference(resolution,[],[f108,f105])).

fof(f105,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f106,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f41,f104])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v3_pre_topc(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v3_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v3_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_pre_topc(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v3_pre_topc(X1,sK0)
            & m1_pre_topc(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_pre_topc(X3,X2)
              & sK1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v3_pre_topc(sK1,sK0)
          & m1_pre_topc(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v3_pre_topc(X3,X2)
            & sK1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
        & v3_pre_topc(sK1,sK0)
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ~ v3_pre_topc(X3,sK2)
          & sK1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & v3_pre_topc(sK1,sK0)
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ~ v3_pre_topc(X3,sK2)
        & sK1 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ v3_pre_topc(sK3,sK2)
      & sK1 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v3_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f102,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f71,f100])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f46,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f43,f96])).

fof(f43,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f70,f92])).

fof(f70,plain,(
    v3_pre_topc(sK3,sK0) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f44,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f45,f88])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f86,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f47,f84])).

fof(f47,plain,(
    ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:11:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (23856)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (23848)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (23840)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (23856)Refutation not found, incomplete strategy% (23856)------------------------------
% 0.22/0.52  % (23856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23837)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (23856)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (23856)Memory used [KB]: 10746
% 0.22/0.52  % (23856)Time elapsed: 0.058 s
% 0.22/0.52  % (23856)------------------------------
% 0.22/0.52  % (23856)------------------------------
% 0.22/0.52  % (23836)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (23834)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (23838)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (23844)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (23839)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (23843)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (23858)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (23852)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (23860)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (23850)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (23842)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (23855)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (23846)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (23845)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (23851)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (23838)Refutation not found, incomplete strategy% (23838)------------------------------
% 0.22/0.54  % (23838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23838)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23838)Memory used [KB]: 6268
% 0.22/0.54  % (23838)Time elapsed: 0.119 s
% 0.22/0.54  % (23838)------------------------------
% 0.22/0.54  % (23838)------------------------------
% 0.22/0.54  % (23836)Refutation not found, incomplete strategy% (23836)------------------------------
% 0.22/0.54  % (23836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (23860)Refutation not found, incomplete strategy% (23860)------------------------------
% 1.36/0.54  % (23860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (23835)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.54  % (23841)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.54  % (23847)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.54  % (23853)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.54  % (23862)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.54  % (23854)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.54  % (23844)Refutation not found, incomplete strategy% (23844)------------------------------
% 1.36/0.54  % (23844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (23844)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (23844)Memory used [KB]: 10746
% 1.36/0.54  % (23844)Time elapsed: 0.130 s
% 1.36/0.54  % (23844)------------------------------
% 1.36/0.54  % (23844)------------------------------
% 1.36/0.54  % (23859)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % (23863)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.55  % (23861)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.55  % (23857)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.55  % (23842)Refutation not found, incomplete strategy% (23842)------------------------------
% 1.36/0.55  % (23842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (23842)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (23842)Memory used [KB]: 10746
% 1.36/0.55  % (23842)Time elapsed: 0.123 s
% 1.36/0.55  % (23842)------------------------------
% 1.36/0.55  % (23842)------------------------------
% 1.36/0.55  % (23849)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.55  % (23860)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (23860)Memory used [KB]: 10746
% 1.36/0.55  % (23860)Time elapsed: 0.117 s
% 1.36/0.55  % (23860)------------------------------
% 1.36/0.55  % (23860)------------------------------
% 1.36/0.56  % (23843)Refutation not found, incomplete strategy% (23843)------------------------------
% 1.36/0.56  % (23843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (23843)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (23843)Memory used [KB]: 10746
% 1.36/0.56  % (23843)Time elapsed: 0.147 s
% 1.36/0.56  % (23843)------------------------------
% 1.36/0.56  % (23843)------------------------------
% 1.36/0.56  % (23851)Refutation not found, incomplete strategy% (23851)------------------------------
% 1.36/0.56  % (23851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (23851)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (23851)Memory used [KB]: 10618
% 1.36/0.56  % (23851)Time elapsed: 0.141 s
% 1.36/0.56  % (23851)------------------------------
% 1.36/0.56  % (23851)------------------------------
% 1.36/0.56  % (23836)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (23836)Memory used [KB]: 10746
% 1.36/0.56  % (23836)Time elapsed: 0.119 s
% 1.36/0.56  % (23836)------------------------------
% 1.36/0.56  % (23836)------------------------------
% 1.51/0.56  % (23853)Refutation found. Thanks to Tanya!
% 1.51/0.56  % SZS status Theorem for theBenchmark
% 1.51/0.57  % (23859)Refutation not found, incomplete strategy% (23859)------------------------------
% 1.51/0.57  % (23859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % SZS output start Proof for theBenchmark
% 1.51/0.58  fof(f349,plain,(
% 1.51/0.58    $false),
% 1.51/0.58    inference(avatar_sat_refutation,[],[f86,f90,f94,f98,f102,f106,f114,f119,f125,f130,f209,f219,f222,f236,f252,f316,f328,f329,f330,f348])).
% 1.51/0.58  % (23859)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (23859)Memory used [KB]: 6524
% 1.51/0.58  % (23859)Time elapsed: 0.161 s
% 1.51/0.58  % (23859)------------------------------
% 1.51/0.58  % (23859)------------------------------
% 1.51/0.58  fof(f348,plain,(
% 1.51/0.58    ~spl7_23 | spl7_1 | ~spl7_19),
% 1.51/0.58    inference(avatar_split_clause,[],[f341,f230,f84,f249])).
% 1.51/0.58  fof(f249,plain,(
% 1.51/0.58    spl7_23 <=> r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2))),
% 1.51/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.51/0.58  fof(f84,plain,(
% 1.51/0.58    spl7_1 <=> v3_pre_topc(sK3,sK2)),
% 1.51/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.51/0.58  fof(f230,plain,(
% 1.51/0.58    spl7_19 <=> v3_pre_topc(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),sK2)),
% 1.51/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.51/0.58  fof(f341,plain,(
% 1.51/0.58    v3_pre_topc(sK3,sK2) | ~r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2)) | ~spl7_19),
% 1.51/0.58    inference(superposition,[],[f231,f160])).
% 1.51/0.58  fof(f160,plain,(
% 1.51/0.58    ( ! [X8,X9] : (k1_setfam_1(k2_tarski(X8,X9)) = X8 | ~r2_hidden(sK6(X8,X9,X8),X9)) )),
% 1.51/0.58    inference(global_subsumption,[],[f132,f155])).
% 1.51/0.58  fof(f155,plain,(
% 1.51/0.58    ( ! [X8,X9] : (~r2_hidden(sK6(X8,X9,X8),X9) | ~r2_hidden(sK6(X8,X9,X8),X8) | k1_setfam_1(k2_tarski(X8,X9)) = X8) )),
% 1.51/0.58    inference(duplicate_literal_removal,[],[f150])).
% 1.51/0.58  fof(f150,plain,(
% 1.51/0.58    ( ! [X8,X9] : (~r2_hidden(sK6(X8,X9,X8),X9) | ~r2_hidden(sK6(X8,X9,X8),X8) | k1_setfam_1(k2_tarski(X8,X9)) = X8 | k1_setfam_1(k2_tarski(X8,X9)) = X8) )),
% 1.51/0.58    inference(resolution,[],[f73,f132])).
% 1.51/0.58  fof(f73,plain,(
% 1.51/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X2) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 1.51/0.58    inference(definition_unfolding,[],[f69,f57])).
% 1.51/0.58  fof(f57,plain,(
% 1.51/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.51/0.58    inference(cnf_transformation,[],[f6])).
% 1.51/0.58  fof(f6,axiom,(
% 1.51/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.51/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.51/0.58  fof(f69,plain,(
% 1.51/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) )),
% 1.51/0.58    inference(cnf_transformation,[],[f40])).
% 1.51/0.58  fof(f40,plain,(
% 1.51/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.51/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).
% 1.51/0.58  fof(f39,plain,(
% 1.51/0.58    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.51/0.58    introduced(choice_axiom,[])).
% 1.51/0.58  fof(f38,plain,(
% 1.51/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.51/0.58    inference(rectify,[],[f37])).
% 1.51/0.58  fof(f37,plain,(
% 1.51/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.51/0.58    inference(flattening,[],[f36])).
% 1.51/0.58  fof(f36,plain,(
% 1.51/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.51/0.58    inference(nnf_transformation,[],[f2])).
% 1.51/0.58  fof(f2,axiom,(
% 1.51/0.58    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.51/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.51/0.58  fof(f132,plain,(
% 1.51/0.58    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1,X0),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.51/0.58    inference(factoring,[],[f75])).
% 1.51/0.58  fof(f75,plain,(
% 1.51/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 1.51/0.58    inference(definition_unfolding,[],[f67,f57])).
% 1.51/0.58  fof(f67,plain,(
% 1.51/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 1.51/0.58    inference(cnf_transformation,[],[f40])).
% 1.51/0.58  fof(f231,plain,(
% 1.51/0.58    v3_pre_topc(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),sK2) | ~spl7_19),
% 1.51/0.58    inference(avatar_component_clause,[],[f230])).
% 1.51/0.58  fof(f330,plain,(
% 1.51/0.58    sK3 != k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) | v3_pre_topc(sK3,sK2) | ~v3_pre_topc(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),sK2)),
% 1.51/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.51/0.58  fof(f329,plain,(
% 1.51/0.58    sK3 != k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) | u1_struct_0(sK2) != k2_struct_0(sK2) | m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.51/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.51/0.58  fof(f328,plain,(
% 1.51/0.58    spl7_27 | spl7_26),
% 1.51/0.58    inference(avatar_split_clause,[],[f319,f314,f324])).
% 1.51/0.58  fof(f324,plain,(
% 1.51/0.58    spl7_27 <=> sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))),
% 1.51/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.51/0.58  fof(f314,plain,(
% 1.51/0.58    spl7_26 <=> r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),sK3)),
% 1.51/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 1.51/0.58  fof(f319,plain,(
% 1.51/0.58    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) | spl7_26),
% 1.51/0.58    inference(resolution,[],[f315,f132])).
% 1.51/0.58  fof(f315,plain,(
% 1.51/0.58    ~r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),sK3) | spl7_26),
% 1.51/0.58    inference(avatar_component_clause,[],[f314])).
% 1.51/0.58  fof(f316,plain,(
% 1.51/0.58    ~spl7_26 | ~spl7_10 | spl7_23),
% 1.51/0.58    inference(avatar_split_clause,[],[f310,f249,f128,f314])).
% 1.51/0.58  fof(f128,plain,(
% 1.51/0.58    spl7_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))),
% 1.51/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.51/0.58  fof(f310,plain,(
% 1.51/0.58    ~r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),sK3) | (~spl7_10 | spl7_23)),
% 1.51/0.58    inference(resolution,[],[f295,f129])).
% 1.51/0.58  fof(f129,plain,(
% 1.51/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | ~spl7_10),
% 1.51/0.58    inference(avatar_component_clause,[],[f128])).
% 1.51/0.58  fof(f295,plain,(
% 1.51/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | ~r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),X1)) ) | spl7_23),
% 1.51/0.58    inference(resolution,[],[f267,f61])).
% 1.51/0.58  fof(f61,plain,(
% 1.51/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.51/0.58    inference(cnf_transformation,[],[f35])).
% 1.51/0.58  fof(f35,plain,(
% 1.51/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.51/0.58    inference(nnf_transformation,[],[f7])).
% 1.51/0.58  fof(f7,axiom,(
% 1.51/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.51/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.51/0.58  fof(f267,plain,(
% 1.51/0.58    ( ! [X2] : (~r1_tarski(X2,k2_struct_0(sK2)) | ~r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),X2)) ) | spl7_23),
% 1.51/0.58    inference(resolution,[],[f250,f58])).
% 1.51/0.58  fof(f58,plain,(
% 1.51/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.51/0.58    inference(cnf_transformation,[],[f34])).
% 1.51/0.58  fof(f34,plain,(
% 1.51/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 1.51/0.58  fof(f33,plain,(
% 1.51/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.51/0.58    introduced(choice_axiom,[])).
% 1.51/0.58  fof(f32,plain,(
% 1.51/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.58    inference(rectify,[],[f31])).
% 1.51/0.58  fof(f31,plain,(
% 1.51/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.58    inference(nnf_transformation,[],[f20])).
% 1.51/0.58  fof(f20,plain,(
% 1.51/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/0.58    inference(ennf_transformation,[],[f1])).
% 1.51/0.58  fof(f1,axiom,(
% 1.51/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.51/0.58  fof(f250,plain,(
% 1.51/0.58    ~r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2)) | spl7_23),
% 1.51/0.58    inference(avatar_component_clause,[],[f249])).
% 1.51/0.58  fof(f252,plain,(
% 1.51/0.58    ~spl7_23 | ~spl7_10 | spl7_20),
% 1.51/0.58    inference(avatar_split_clause,[],[f242,f234,f128,f249])).
% 1.51/0.58  fof(f234,plain,(
% 1.51/0.58    spl7_20 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))),
% 1.51/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.51/0.58  fof(f242,plain,(
% 1.51/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | ~r2_hidden(sK6(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2)) | spl7_20),
% 1.51/0.58    inference(superposition,[],[f235,f160])).
% 1.51/0.58  fof(f235,plain,(
% 1.51/0.58    ~m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | spl7_20),
% 1.51/0.58    inference(avatar_component_clause,[],[f234])).
% 1.51/0.58  fof(f236,plain,(
% 1.51/0.58    spl7_19 | ~spl7_8 | ~spl7_20 | ~spl7_3 | ~spl7_17),
% 1.51/0.58    inference(avatar_split_clause,[],[f227,f217,f92,f234,f117,f230])).
% 1.51/0.58  fof(f117,plain,(
% 1.51/0.58    spl7_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.51/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.51/0.58  fof(f92,plain,(
% 1.51/0.58    spl7_3 <=> v3_pre_topc(sK3,sK0)),
% 1.51/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.51/0.58  fof(f217,plain,(
% 1.51/0.58    spl7_17 <=> ! [X0] : (v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2) | ~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0))),
% 1.51/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.51/0.58  fof(f227,plain,(
% 1.51/0.58    ~m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),sK2) | (~spl7_3 | ~spl7_17)),
% 1.51/0.58    inference(resolution,[],[f218,f93])).
% 1.51/0.58  fof(f93,plain,(
% 1.51/0.58    v3_pre_topc(sK3,sK0) | ~spl7_3),
% 1.51/0.58    inference(avatar_component_clause,[],[f92])).
% 1.51/0.58  fof(f218,plain,(
% 1.51/0.58    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2)) ) | ~spl7_17),
% 1.51/0.58    inference(avatar_component_clause,[],[f217])).
% 1.51/0.58  fof(f222,plain,(
% 1.51/0.58    spl7_16),
% 1.51/0.58    inference(avatar_contradiction_clause,[],[f220])).
% 1.51/0.58  fof(f220,plain,(
% 1.51/0.58    $false | spl7_16),
% 1.51/0.58    inference(resolution,[],[f215,f107])).
% 1.51/0.59  fof(f107,plain,(
% 1.51/0.59    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.51/0.59    inference(forward_demodulation,[],[f49,f48])).
% 1.51/0.59  fof(f48,plain,(
% 1.51/0.59    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.51/0.59    inference(cnf_transformation,[],[f3])).
% 1.51/0.59  fof(f3,axiom,(
% 1.51/0.59    ! [X0] : k2_subset_1(X0) = X0),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.51/0.59  fof(f49,plain,(
% 1.51/0.59    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.51/0.59    inference(cnf_transformation,[],[f4])).
% 1.51/0.59  fof(f4,axiom,(
% 1.51/0.59    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.51/0.59  fof(f215,plain,(
% 1.51/0.59    ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | spl7_16),
% 1.51/0.59    inference(avatar_component_clause,[],[f214])).
% 1.51/0.59  fof(f214,plain,(
% 1.51/0.59    spl7_16 <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.51/0.59  fof(f219,plain,(
% 1.51/0.59    ~spl7_16 | spl7_17 | ~spl7_15),
% 1.51/0.59    inference(avatar_split_clause,[],[f211,f207,f217,f214])).
% 1.51/0.59  fof(f207,plain,(
% 1.51/0.59    spl7_15 <=> ! [X0] : (v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))))),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.51/0.59  fof(f211,plain,(
% 1.51/0.59    ( ! [X0] : (v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))) ) | ~spl7_15),
% 1.51/0.59    inference(superposition,[],[f208,f72])).
% 1.51/0.59  fof(f72,plain,(
% 1.51/0.59    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.51/0.59    inference(definition_unfolding,[],[f63,f57])).
% 1.51/0.59  fof(f63,plain,(
% 1.51/0.59    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.51/0.59    inference(cnf_transformation,[],[f21])).
% 1.51/0.59  fof(f21,plain,(
% 1.51/0.59    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.51/0.59    inference(ennf_transformation,[],[f5])).
% 1.51/0.59  fof(f5,axiom,(
% 1.51/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.51/0.59  fof(f208,plain,(
% 1.51/0.59    ( ! [X0] : (v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))) ) | ~spl7_15),
% 1.51/0.59    inference(avatar_component_clause,[],[f207])).
% 1.51/0.59  fof(f209,plain,(
% 1.51/0.59    ~spl7_6 | spl7_15 | ~spl7_4 | ~spl7_7 | ~spl7_9),
% 1.51/0.59    inference(avatar_split_clause,[],[f205,f123,f112,f96,f207,f104])).
% 1.51/0.59  fof(f104,plain,(
% 1.51/0.59    spl7_6 <=> l1_pre_topc(sK0)),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.51/0.59  fof(f96,plain,(
% 1.51/0.59    spl7_4 <=> m1_pre_topc(sK2,sK0)),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.51/0.59  fof(f112,plain,(
% 1.51/0.59    spl7_7 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.51/0.59  fof(f123,plain,(
% 1.51/0.59    spl7_9 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.51/0.59  fof(f205,plain,(
% 1.51/0.59    ( ! [X0] : (v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | (~spl7_4 | ~spl7_7 | ~spl7_9)),
% 1.51/0.59    inference(forward_demodulation,[],[f204,f124])).
% 1.51/0.59  fof(f124,plain,(
% 1.51/0.59    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl7_9),
% 1.51/0.59    inference(avatar_component_clause,[],[f123])).
% 1.51/0.59  fof(f204,plain,(
% 1.51/0.59    ( ! [X0] : (~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~l1_pre_topc(sK0)) ) | (~spl7_4 | ~spl7_7 | ~spl7_9)),
% 1.51/0.59    inference(forward_demodulation,[],[f203,f124])).
% 1.51/0.59  fof(f203,plain,(
% 1.51/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~l1_pre_topc(sK0)) ) | (~spl7_4 | ~spl7_7)),
% 1.51/0.59    inference(forward_demodulation,[],[f202,f113])).
% 1.51/0.59  fof(f113,plain,(
% 1.51/0.59    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl7_7),
% 1.51/0.59    inference(avatar_component_clause,[],[f112])).
% 1.51/0.59  fof(f202,plain,(
% 1.51/0.59    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~l1_pre_topc(sK0)) ) | ~spl7_4),
% 1.51/0.59    inference(resolution,[],[f79,f97])).
% 1.51/0.59  fof(f97,plain,(
% 1.51/0.59    m1_pre_topc(sK2,sK0) | ~spl7_4),
% 1.51/0.59    inference(avatar_component_clause,[],[f96])).
% 1.51/0.59  fof(f79,plain,(
% 1.51/0.59    ( ! [X0,X3,X1] : (~m1_pre_topc(X1,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~l1_pre_topc(X0)) )),
% 1.51/0.59    inference(equality_resolution,[],[f56])).
% 1.51/0.59  fof(f56,plain,(
% 1.51/0.59    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f30])).
% 1.51/0.59  fof(f30,plain,(
% 1.51/0.59    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.51/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 1.51/0.59  fof(f29,plain,(
% 1.51/0.59    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.51/0.59    introduced(choice_axiom,[])).
% 1.51/0.59  fof(f28,plain,(
% 1.51/0.59    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.51/0.59    inference(rectify,[],[f27])).
% 1.51/0.59  fof(f27,plain,(
% 1.51/0.59    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.51/0.59    inference(nnf_transformation,[],[f19])).
% 1.51/0.59  fof(f19,plain,(
% 1.51/0.59    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.51/0.59    inference(ennf_transformation,[],[f11])).
% 1.51/0.59  fof(f11,axiom,(
% 1.51/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).
% 1.51/0.59  fof(f130,plain,(
% 1.51/0.59    spl7_10 | ~spl7_2 | ~spl7_9),
% 1.51/0.59    inference(avatar_split_clause,[],[f126,f123,f88,f128])).
% 1.51/0.59  fof(f88,plain,(
% 1.51/0.59    spl7_2 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.51/0.59  fof(f126,plain,(
% 1.51/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | (~spl7_2 | ~spl7_9)),
% 1.51/0.59    inference(superposition,[],[f89,f124])).
% 1.51/0.59  fof(f89,plain,(
% 1.51/0.59    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl7_2),
% 1.51/0.59    inference(avatar_component_clause,[],[f88])).
% 1.51/0.59  fof(f125,plain,(
% 1.51/0.59    ~spl7_6 | spl7_9 | ~spl7_4),
% 1.51/0.59    inference(avatar_split_clause,[],[f120,f96,f123,f104])).
% 1.51/0.59  fof(f120,plain,(
% 1.51/0.59    u1_struct_0(sK2) = k2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~spl7_4),
% 1.51/0.59    inference(resolution,[],[f110,f97])).
% 1.51/0.59  fof(f110,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X1)) )),
% 1.51/0.59    inference(resolution,[],[f108,f52])).
% 1.51/0.59  fof(f52,plain,(
% 1.51/0.59    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f18])).
% 1.51/0.59  fof(f18,plain,(
% 1.51/0.59    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.51/0.59    inference(ennf_transformation,[],[f10])).
% 1.51/0.59  fof(f10,axiom,(
% 1.51/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.51/0.59  fof(f108,plain,(
% 1.51/0.59    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.51/0.59    inference(resolution,[],[f50,f51])).
% 1.51/0.59  fof(f51,plain,(
% 1.51/0.59    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f17])).
% 1.51/0.59  fof(f17,plain,(
% 1.51/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.51/0.59    inference(ennf_transformation,[],[f9])).
% 1.51/0.59  fof(f9,axiom,(
% 1.51/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.51/0.59  fof(f50,plain,(
% 1.51/0.59    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f16])).
% 1.51/0.59  fof(f16,plain,(
% 1.51/0.59    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.51/0.59    inference(ennf_transformation,[],[f8])).
% 1.51/0.59  fof(f8,axiom,(
% 1.51/0.59    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.51/0.59  fof(f119,plain,(
% 1.51/0.59    spl7_8 | ~spl7_5 | ~spl7_7),
% 1.51/0.59    inference(avatar_split_clause,[],[f115,f112,f100,f117])).
% 1.51/0.59  fof(f100,plain,(
% 1.51/0.59    spl7_5 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.51/0.59  fof(f115,plain,(
% 1.51/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl7_5 | ~spl7_7)),
% 1.51/0.59    inference(superposition,[],[f101,f113])).
% 1.51/0.59  fof(f101,plain,(
% 1.51/0.59    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_5),
% 1.51/0.59    inference(avatar_component_clause,[],[f100])).
% 1.51/0.59  fof(f114,plain,(
% 1.51/0.59    spl7_7 | ~spl7_6),
% 1.51/0.59    inference(avatar_split_clause,[],[f109,f104,f112])).
% 1.51/0.59  fof(f109,plain,(
% 1.51/0.59    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl7_6),
% 1.51/0.59    inference(resolution,[],[f108,f105])).
% 1.51/0.59  fof(f105,plain,(
% 1.51/0.59    l1_pre_topc(sK0) | ~spl7_6),
% 1.51/0.59    inference(avatar_component_clause,[],[f104])).
% 1.51/0.59  fof(f106,plain,(
% 1.51/0.59    spl7_6),
% 1.51/0.59    inference(avatar_split_clause,[],[f41,f104])).
% 1.51/0.59  fof(f41,plain,(
% 1.51/0.59    l1_pre_topc(sK0)),
% 1.51/0.59    inference(cnf_transformation,[],[f26])).
% 1.51/0.59  fof(f26,plain,(
% 1.51/0.59    (((~v3_pre_topc(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & v3_pre_topc(sK1,sK0) & m1_pre_topc(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.51/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f25,f24,f23,f22])).
% 1.51/0.59  fof(f22,plain,(
% 1.51/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.51/0.59    introduced(choice_axiom,[])).
% 1.51/0.59  fof(f23,plain,(
% 1.51/0.59    ? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.51/0.59    introduced(choice_axiom,[])).
% 1.51/0.59  fof(f24,plain,(
% 1.51/0.59    ? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK1,sK0) & m1_pre_topc(X2,sK0)) => (? [X3] : (~v3_pre_topc(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & v3_pre_topc(sK1,sK0) & m1_pre_topc(sK2,sK0))),
% 1.51/0.59    introduced(choice_axiom,[])).
% 1.51/0.59  fof(f25,plain,(
% 1.51/0.59    ? [X3] : (~v3_pre_topc(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) => (~v3_pre_topc(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.51/0.59    introduced(choice_axiom,[])).
% 1.51/0.59  fof(f15,plain,(
% 1.51/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.51/0.59    inference(flattening,[],[f14])).
% 1.51/0.59  fof(f14,plain,(
% 1.51/0.59    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v3_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.51/0.59    inference(ennf_transformation,[],[f13])).
% 1.51/0.59  fof(f13,negated_conjecture,(
% 1.51/0.59    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 1.51/0.59    inference(negated_conjecture,[],[f12])).
% 1.51/0.59  fof(f12,conjecture,(
% 1.51/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).
% 1.51/0.59  fof(f102,plain,(
% 1.51/0.59    spl7_5),
% 1.51/0.59    inference(avatar_split_clause,[],[f71,f100])).
% 1.51/0.59  fof(f71,plain,(
% 1.51/0.59    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.51/0.59    inference(definition_unfolding,[],[f42,f46])).
% 1.51/0.59  fof(f46,plain,(
% 1.51/0.59    sK1 = sK3),
% 1.51/0.59    inference(cnf_transformation,[],[f26])).
% 1.51/0.59  fof(f42,plain,(
% 1.51/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.51/0.59    inference(cnf_transformation,[],[f26])).
% 1.51/0.59  fof(f98,plain,(
% 1.51/0.59    spl7_4),
% 1.51/0.59    inference(avatar_split_clause,[],[f43,f96])).
% 1.51/0.59  fof(f43,plain,(
% 1.51/0.59    m1_pre_topc(sK2,sK0)),
% 1.51/0.59    inference(cnf_transformation,[],[f26])).
% 1.51/0.59  fof(f94,plain,(
% 1.51/0.59    spl7_3),
% 1.51/0.59    inference(avatar_split_clause,[],[f70,f92])).
% 1.51/0.59  fof(f70,plain,(
% 1.51/0.59    v3_pre_topc(sK3,sK0)),
% 1.51/0.59    inference(definition_unfolding,[],[f44,f46])).
% 1.51/0.59  fof(f44,plain,(
% 1.51/0.59    v3_pre_topc(sK1,sK0)),
% 1.51/0.59    inference(cnf_transformation,[],[f26])).
% 1.51/0.59  fof(f90,plain,(
% 1.51/0.59    spl7_2),
% 1.51/0.59    inference(avatar_split_clause,[],[f45,f88])).
% 1.51/0.59  fof(f45,plain,(
% 1.51/0.59    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.51/0.59    inference(cnf_transformation,[],[f26])).
% 1.51/0.59  fof(f86,plain,(
% 1.51/0.59    ~spl7_1),
% 1.51/0.59    inference(avatar_split_clause,[],[f47,f84])).
% 1.51/0.59  fof(f47,plain,(
% 1.51/0.59    ~v3_pre_topc(sK3,sK2)),
% 1.51/0.59    inference(cnf_transformation,[],[f26])).
% 1.51/0.59  % SZS output end Proof for theBenchmark
% 1.51/0.59  % (23853)------------------------------
% 1.51/0.59  % (23853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.59  % (23853)Termination reason: Refutation
% 1.51/0.59  
% 1.51/0.59  % (23853)Memory used [KB]: 11001
% 1.51/0.59  % (23853)Time elapsed: 0.140 s
% 1.51/0.59  % (23853)------------------------------
% 1.51/0.59  % (23853)------------------------------
% 1.51/0.59  % (23832)Success in time 0.214 s
%------------------------------------------------------------------------------
