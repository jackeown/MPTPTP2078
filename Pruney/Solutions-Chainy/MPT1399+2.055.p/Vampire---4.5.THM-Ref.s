%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 369 expanded)
%              Number of leaves         :   40 ( 139 expanded)
%              Depth                    :   17
%              Number of atoms          :  563 (3038 expanded)
%              Number of equality atoms :   58 ( 264 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f612,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f112,f178,f199,f210,f212,f214,f220,f257,f261,f401,f425,f560,f571,f576,f597,f611])).

fof(f611,plain,
    ( ~ spl5_6
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_17 ),
    inference(resolution,[],[f131,f195])).

fof(f195,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl5_17
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f131,plain,
    ( r2_hidden(u1_struct_0(sK0),sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_6
  <=> r2_hidden(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f597,plain,
    ( ~ spl5_1
    | ~ spl5_19
    | spl5_21
    | ~ spl5_20
    | ~ spl5_39
    | ~ spl5_41
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f593,f519,f423,f384,f207,f234,f203,f103])).

fof(f103,plain,
    ( spl5_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f203,plain,
    ( spl5_19
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f234,plain,
    ( spl5_21
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f207,plain,
    ( spl5_20
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f384,plain,
    ( spl5_39
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f423,plain,
    ( spl5_41
  <=> ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v1_xboole_0(u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f519,plain,
    ( spl5_45
  <=> sK2 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f593,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl5_41
    | ~ spl5_45 ),
    inference(superposition,[],[f438,f521])).

fof(f521,plain,
    ( sK2 = k2_struct_0(sK0)
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f519])).

fof(f438,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_struct_0(X0) )
    | ~ spl5_41 ),
    inference(superposition,[],[f424,f70])).

fof(f70,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f424,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f423])).

fof(f576,plain,(
    ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f575])).

fof(f575,plain,
    ( $false
    | ~ spl5_18 ),
    inference(resolution,[],[f198,f89])).

fof(f89,plain,(
    v1_xboole_0(sK2) ),
    inference(definition_unfolding,[],[f63,f62])).

fof(f62,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( k1_xboole_0 = sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ v3_pre_topc(X3,sK0) )
          & ( ( r2_hidden(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & v3_pre_topc(X3,sK0) )
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK0)
                      | ~ v3_pre_topc(X3,sK0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK0)
                        & v3_pre_topc(X3,sK0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,sK0)
                    | ~ v3_pre_topc(X3,sK0) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,sK0)
                      & v3_pre_topc(X3,sK0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(sK1,X3)
                  | ~ v4_pre_topc(X3,sK0)
                  | ~ v3_pre_topc(X3,sK0) )
                & ( ( r2_hidden(sK1,X3)
                    & v4_pre_topc(X3,sK0)
                    & v3_pre_topc(X3,sK0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( k1_xboole_0 = X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(sK1,X3)
                | ~ v4_pre_topc(X3,sK0)
                | ~ v3_pre_topc(X3,sK0) )
              & ( ( r2_hidden(sK1,X3)
                  & v4_pre_topc(X3,sK0)
                  & v3_pre_topc(X3,sK0) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK2)
              | ~ r2_hidden(sK1,X3)
              | ~ v4_pre_topc(X3,sK0)
              | ~ v3_pre_topc(X3,sK0) )
            & ( ( r2_hidden(sK1,X3)
                & v4_pre_topc(X3,sK0)
                & v3_pre_topc(X3,sK0) )
              | ~ r2_hidden(X3,sK2) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f198,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl5_18
  <=> ! [X0] : ~ v1_xboole_0(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f571,plain,
    ( spl5_45
    | ~ spl5_2
    | spl5_16
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f512,f194,f187,f107,f519])).

fof(f107,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f187,plain,
    ( spl5_16
  <=> r2_hidden(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f512,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | sK2 = k2_struct_0(sK0)
    | spl5_16
    | ~ spl5_17 ),
    inference(resolution,[],[f490,f189])).

fof(f189,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f187])).

fof(f490,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,X1)
        | sK2 = X1 )
    | ~ spl5_17 ),
    inference(resolution,[],[f428,f195])).

fof(f428,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1)
      | sK2 = X1 ) ),
    inference(resolution,[],[f295,f91])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f66,f62])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f295,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | sK2 = X0 ) ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | sK2 = X0
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f94,f266])).

fof(f266,plain,(
    ! [X0] :
      ( k3_subset_1(X0,sK2) = X0
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f265,f93])).

fof(f93,plain,(
    ! [X0] : k5_xboole_0(X0,sK2) = X0 ),
    inference(definition_unfolding,[],[f68,f62])).

fof(f68,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f265,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,sK2) = k3_subset_1(X0,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f96,f92])).

fof(f92,plain,(
    ! [X0] : sK2 = k1_setfam_1(k1_enumset1(X0,X0,sK2)) ),
    inference(definition_unfolding,[],[f67,f62,f87,f62])).

fof(f87,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f80,f81])).

fof(f81,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f96,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f83,f88])).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f82,f87])).

fof(f82,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sK2 = X0 ) ),
    inference(definition_unfolding,[],[f72,f62])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

fof(f560,plain,
    ( ~ spl5_16
    | ~ spl5_15
    | ~ spl5_13
    | spl5_14
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f350,f255,f175,f169,f181,f187])).

fof(f181,plain,
    ( spl5_15
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f169,plain,
    ( spl5_13
  <=> v3_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f175,plain,
    ( spl5_14
  <=> r2_hidden(k2_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f255,plain,
    ( spl5_26
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X0,sK2)
        | ~ v3_pre_topc(X0,sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ r2_hidden(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f350,plain,
    ( r2_hidden(k2_struct_0(sK0),sK2)
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ spl5_26 ),
    inference(resolution,[],[f256,f98])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f69,f65])).

fof(f65,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f256,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X0,sK2)
        | ~ v3_pre_topc(X0,sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ r2_hidden(sK1,X0) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f255])).

fof(f425,plain,
    ( spl5_41
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f420,f384,f423])).

fof(f420,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f405])).

fof(f405,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(superposition,[],[f74,f343])).

fof(f343,plain,(
    ! [X0] :
      ( sK2 = sK3(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f225,f95])).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | sK2 = X0 ) ),
    inference(definition_unfolding,[],[f79,f62])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f225,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,sK3(X2))
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ v1_xboole_0(u1_struct_0(X2))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f73,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK3(X0),X0)
        & v3_pre_topc(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK3(X0),X0)
        & v3_pre_topc(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f401,plain,(
    spl5_39 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | spl5_39 ),
    inference(resolution,[],[f386,f89])).

fof(f386,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_39 ),
    inference(avatar_component_clause,[],[f384])).

fof(f261,plain,(
    ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl5_21 ),
    inference(resolution,[],[f236,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f236,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f234])).

fof(f257,plain,
    ( ~ spl5_1
    | spl5_26 ),
    inference(avatar_split_clause,[],[f232,f255,f103])).

fof(f232,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(sK1,X0)
      | ~ v4_pre_topc(X0,sK0)
      | ~ v3_pre_topc(X0,sK0)
      | r2_hidden(X0,sK2)
      | ~ l1_struct_0(sK0) ) ),
    inference(superposition,[],[f61,f70])).

fof(f61,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f220,plain,
    ( ~ spl5_19
    | ~ spl5_20
    | spl5_15 ),
    inference(avatar_split_clause,[],[f219,f181,f207,f203])).

fof(f219,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_15 ),
    inference(resolution,[],[f183,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f183,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f181])).

fof(f214,plain,(
    spl5_20 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | spl5_20 ),
    inference(resolution,[],[f209,f55])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f209,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f207])).

fof(f212,plain,(
    spl5_19 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl5_19 ),
    inference(resolution,[],[f205,f54])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f205,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f203])).

fof(f210,plain,
    ( ~ spl5_19
    | ~ spl5_20
    | spl5_13 ),
    inference(avatar_split_clause,[],[f201,f169,f207,f203])).

fof(f201,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_13 ),
    inference(resolution,[],[f171,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f171,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f169])).

fof(f199,plain,
    ( spl5_17
    | spl5_18 ),
    inference(avatar_split_clause,[],[f191,f197,f194])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f86,f91])).

fof(f178,plain,
    ( ~ spl5_1
    | ~ spl5_14
    | spl5_6 ),
    inference(avatar_split_clause,[],[f173,f130,f175,f103])).

fof(f173,plain,
    ( ~ r2_hidden(k2_struct_0(sK0),sK2)
    | ~ l1_struct_0(sK0)
    | spl5_6 ),
    inference(superposition,[],[f132,f70])).

fof(f132,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f112,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f105,f97])).

fof(f97,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f71,f55])).

fof(f71,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f105,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f110,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f101,f107,f103])).

fof(f101,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f56,f70])).

fof(f56,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (25960)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.42  % (25960)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f612,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f110,f112,f178,f199,f210,f212,f214,f220,f257,f261,f401,f425,f560,f571,f576,f597,f611])).
% 0.20/0.42  fof(f611,plain,(
% 0.20/0.42    ~spl5_6 | ~spl5_17),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f605])).
% 0.20/0.42  fof(f605,plain,(
% 0.20/0.42    $false | (~spl5_6 | ~spl5_17)),
% 0.20/0.42    inference(resolution,[],[f131,f195])).
% 0.20/0.42  fof(f195,plain,(
% 0.20/0.42    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | ~spl5_17),
% 0.20/0.42    inference(avatar_component_clause,[],[f194])).
% 0.20/0.42  fof(f194,plain,(
% 0.20/0.42    spl5_17 <=> ! [X1] : ~r2_hidden(X1,sK2)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.42  fof(f131,plain,(
% 0.20/0.42    r2_hidden(u1_struct_0(sK0),sK2) | ~spl5_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f130])).
% 0.20/0.42  fof(f130,plain,(
% 0.20/0.42    spl5_6 <=> r2_hidden(u1_struct_0(sK0),sK2)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.42  fof(f597,plain,(
% 0.20/0.42    ~spl5_1 | ~spl5_19 | spl5_21 | ~spl5_20 | ~spl5_39 | ~spl5_41 | ~spl5_45),
% 0.20/0.42    inference(avatar_split_clause,[],[f593,f519,f423,f384,f207,f234,f203,f103])).
% 0.20/0.42  fof(f103,plain,(
% 0.20/0.42    spl5_1 <=> l1_struct_0(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.42  fof(f203,plain,(
% 0.20/0.42    spl5_19 <=> v2_pre_topc(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.42  fof(f234,plain,(
% 0.20/0.42    spl5_21 <=> v2_struct_0(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.42  fof(f207,plain,(
% 0.20/0.42    spl5_20 <=> l1_pre_topc(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.42  fof(f384,plain,(
% 0.20/0.42    spl5_39 <=> v1_xboole_0(sK2)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.20/0.42  fof(f423,plain,(
% 0.20/0.42    spl5_41 <=> ! [X1] : (~l1_pre_topc(X1) | ~v1_xboole_0(u1_struct_0(X1)) | v2_struct_0(X1) | ~v2_pre_topc(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.20/0.42  fof(f519,plain,(
% 0.20/0.42    spl5_45 <=> sK2 = k2_struct_0(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 0.20/0.42  fof(f593,plain,(
% 0.20/0.42    ~v1_xboole_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_struct_0(sK0) | (~spl5_41 | ~spl5_45)),
% 0.20/0.42    inference(superposition,[],[f438,f521])).
% 0.20/0.42  fof(f521,plain,(
% 0.20/0.42    sK2 = k2_struct_0(sK0) | ~spl5_45),
% 0.20/0.42    inference(avatar_component_clause,[],[f519])).
% 0.20/0.42  fof(f438,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_struct_0(X0)) ) | ~spl5_41),
% 0.20/0.42    inference(superposition,[],[f424,f70])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f27])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,axiom,(
% 0.20/0.42    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.42  fof(f424,plain,(
% 0.20/0.42    ( ! [X1] : (~v1_xboole_0(u1_struct_0(X1)) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(X1)) ) | ~spl5_41),
% 0.20/0.42    inference(avatar_component_clause,[],[f423])).
% 0.20/0.42  fof(f576,plain,(
% 0.20/0.42    ~spl5_18),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f575])).
% 0.20/0.42  fof(f575,plain,(
% 0.20/0.42    $false | ~spl5_18),
% 0.20/0.42    inference(resolution,[],[f198,f89])).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    v1_xboole_0(sK2)),
% 0.20/0.42    inference(definition_unfolding,[],[f63,f62])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    k1_xboole_0 = sK2),
% 0.20/0.42    inference(cnf_transformation,[],[f48])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f47,f46,f45])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f43])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.43    inference(nnf_transformation,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f23])).
% 0.20/0.43  fof(f23,negated_conjecture,(
% 0.20/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.20/0.43    inference(negated_conjecture,[],[f22])).
% 0.20/0.43  fof(f22,conjecture,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.43  fof(f198,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl5_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f197])).
% 0.20/0.43  fof(f197,plain,(
% 0.20/0.43    spl5_18 <=> ! [X0] : ~v1_xboole_0(X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.43  fof(f571,plain,(
% 0.20/0.43    spl5_45 | ~spl5_2 | spl5_16 | ~spl5_17),
% 0.20/0.43    inference(avatar_split_clause,[],[f512,f194,f187,f107,f519])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    spl5_2 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.43  fof(f187,plain,(
% 0.20/0.43    spl5_16 <=> r2_hidden(sK1,k2_struct_0(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.43  fof(f512,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,k2_struct_0(sK0)) | sK2 = k2_struct_0(sK0) | (spl5_16 | ~spl5_17)),
% 0.20/0.43    inference(resolution,[],[f490,f189])).
% 0.20/0.43  fof(f189,plain,(
% 0.20/0.43    ~r2_hidden(sK1,k2_struct_0(sK0)) | spl5_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f187])).
% 0.20/0.43  fof(f490,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~m1_subset_1(X0,X1) | sK2 = X1) ) | ~spl5_17),
% 0.20/0.43    inference(resolution,[],[f428,f195])).
% 0.20/0.43  fof(f428,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK2 = X1) )),
% 0.20/0.43    inference(resolution,[],[f295,f91])).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f66,f62])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.43  fof(f295,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | r2_hidden(X1,sK2) | ~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | sK2 = X0) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f294])).
% 0.20/0.43  fof(f294,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_hidden(X1,X0) | r2_hidden(X1,sK2) | ~m1_subset_1(X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | sK2 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(superposition,[],[f94,f266])).
% 0.20/0.43  fof(f266,plain,(
% 0.20/0.43    ( ! [X0] : (k3_subset_1(X0,sK2) = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f265,f93])).
% 0.20/0.43  fof(f93,plain,(
% 0.20/0.43    ( ! [X0] : (k5_xboole_0(X0,sK2) = X0) )),
% 0.20/0.43    inference(definition_unfolding,[],[f68,f62])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.43  fof(f265,plain,(
% 0.20/0.43    ( ! [X0] : (k5_xboole_0(X0,sK2) = k3_subset_1(X0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(superposition,[],[f96,f92])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    ( ! [X0] : (sK2 = k1_setfam_1(k1_enumset1(X0,X0,sK2))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f67,f62,f87,f62])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f80,f81])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.43  fof(f96,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f83,f88])).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f82,f87])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f38])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.43  fof(f94,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK2 = X0) )),
% 0.20/0.43    inference(definition_unfolding,[],[f72,f62])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.20/0.43    inference(flattening,[],[f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.20/0.43    inference(ennf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).
% 0.20/0.43  fof(f560,plain,(
% 0.20/0.43    ~spl5_16 | ~spl5_15 | ~spl5_13 | spl5_14 | ~spl5_26),
% 0.20/0.43    inference(avatar_split_clause,[],[f350,f255,f175,f169,f181,f187])).
% 0.20/0.43  fof(f181,plain,(
% 0.20/0.43    spl5_15 <=> v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.43  fof(f169,plain,(
% 0.20/0.43    spl5_13 <=> v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.43  fof(f175,plain,(
% 0.20/0.43    spl5_14 <=> r2_hidden(k2_struct_0(sK0),sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.43  fof(f255,plain,(
% 0.20/0.43    spl5_26 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X0,sK2) | ~v3_pre_topc(X0,sK0) | ~v4_pre_topc(X0,sK0) | ~r2_hidden(sK1,X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.20/0.43  fof(f350,plain,(
% 0.20/0.43    r2_hidden(k2_struct_0(sK0),sK2) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~r2_hidden(sK1,k2_struct_0(sK0)) | ~spl5_26),
% 0.20/0.43    inference(resolution,[],[f256,f98])).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f69,f65])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.43  fof(f256,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X0,sK2) | ~v3_pre_topc(X0,sK0) | ~v4_pre_topc(X0,sK0) | ~r2_hidden(sK1,X0)) ) | ~spl5_26),
% 0.20/0.43    inference(avatar_component_clause,[],[f255])).
% 0.20/0.43  fof(f425,plain,(
% 0.20/0.43    spl5_41 | ~spl5_39),
% 0.20/0.43    inference(avatar_split_clause,[],[f420,f384,f423])).
% 0.20/0.43  fof(f420,plain,(
% 0.20/0.43    ( ! [X1] : (~v1_xboole_0(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v1_xboole_0(u1_struct_0(X1))) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f405])).
% 0.20/0.43  fof(f405,plain,(
% 0.20/0.43    ( ! [X1] : (~v1_xboole_0(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(X1) | ~v1_xboole_0(u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.20/0.43    inference(superposition,[],[f74,f343])).
% 0.20/0.43  fof(f343,plain,(
% 0.20/0.43    ( ! [X0] : (sK2 = sK3(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.43    inference(resolution,[],[f225,f95])).
% 0.20/0.43  fof(f95,plain,(
% 0.20/0.43    ( ! [X0] : (r2_hidden(sK4(X0),X0) | sK2 = X0) )),
% 0.20/0.43    inference(definition_unfolding,[],[f79,f62])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.43    inference(ennf_transformation,[],[f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.43    inference(pure_predicate_removal,[],[f16])).
% 0.20/0.43  fof(f16,axiom,(
% 0.20/0.43    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.20/0.43  fof(f225,plain,(
% 0.20/0.43    ( ! [X2,X3] : (~r2_hidden(X3,sK3(X2)) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~v1_xboole_0(u1_struct_0(X2)) | ~l1_pre_topc(X2)) )),
% 0.20/0.43    inference(resolution,[],[f73,f86])).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ! [X0] : ((v4_pre_topc(sK3(X0),X0) & v3_pre_topc(sK3(X0),X0) & ~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f49])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK3(X0),X0) & v3_pre_topc(sK3(X0),X0) & ~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f50])).
% 0.20/0.43  fof(f401,plain,(
% 0.20/0.43    spl5_39),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f398])).
% 0.20/0.43  fof(f398,plain,(
% 0.20/0.43    $false | spl5_39),
% 0.20/0.43    inference(resolution,[],[f386,f89])).
% 0.20/0.43  fof(f386,plain,(
% 0.20/0.43    ~v1_xboole_0(sK2) | spl5_39),
% 0.20/0.43    inference(avatar_component_clause,[],[f384])).
% 0.20/0.43  fof(f261,plain,(
% 0.20/0.43    ~spl5_21),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f260])).
% 0.20/0.43  fof(f260,plain,(
% 0.20/0.43    $false | ~spl5_21),
% 0.20/0.43    inference(resolution,[],[f236,f53])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    ~v2_struct_0(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f48])).
% 0.20/0.43  fof(f236,plain,(
% 0.20/0.43    v2_struct_0(sK0) | ~spl5_21),
% 0.20/0.43    inference(avatar_component_clause,[],[f234])).
% 0.20/0.43  fof(f257,plain,(
% 0.20/0.43    ~spl5_1 | spl5_26),
% 0.20/0.43    inference(avatar_split_clause,[],[f232,f255,f103])).
% 0.20/0.43  fof(f232,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(sK1,X0) | ~v4_pre_topc(X0,sK0) | ~v3_pre_topc(X0,sK0) | r2_hidden(X0,sK2) | ~l1_struct_0(sK0)) )),
% 0.20/0.43    inference(superposition,[],[f61,f70])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | r2_hidden(X3,sK2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f48])).
% 0.20/0.43  fof(f220,plain,(
% 0.20/0.43    ~spl5_19 | ~spl5_20 | spl5_15),
% 0.20/0.43    inference(avatar_split_clause,[],[f219,f181,f207,f203])).
% 0.20/0.43  fof(f219,plain,(
% 0.20/0.43    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_15),
% 0.20/0.43    inference(resolution,[],[f183,f77])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f33])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.20/0.43  fof(f183,plain,(
% 0.20/0.43    ~v4_pre_topc(k2_struct_0(sK0),sK0) | spl5_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f181])).
% 0.20/0.43  fof(f214,plain,(
% 0.20/0.43    spl5_20),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f213])).
% 0.20/0.43  fof(f213,plain,(
% 0.20/0.43    $false | spl5_20),
% 0.20/0.43    inference(resolution,[],[f209,f55])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    l1_pre_topc(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f48])).
% 0.20/0.43  fof(f209,plain,(
% 0.20/0.43    ~l1_pre_topc(sK0) | spl5_20),
% 0.20/0.43    inference(avatar_component_clause,[],[f207])).
% 0.20/0.43  fof(f212,plain,(
% 0.20/0.43    spl5_19),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f211])).
% 0.20/0.43  fof(f211,plain,(
% 0.20/0.43    $false | spl5_19),
% 0.20/0.43    inference(resolution,[],[f205,f54])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    v2_pre_topc(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f48])).
% 0.20/0.43  fof(f205,plain,(
% 0.20/0.43    ~v2_pre_topc(sK0) | spl5_19),
% 0.20/0.43    inference(avatar_component_clause,[],[f203])).
% 0.20/0.43  fof(f210,plain,(
% 0.20/0.43    ~spl5_19 | ~spl5_20 | spl5_13),
% 0.20/0.43    inference(avatar_split_clause,[],[f201,f169,f207,f203])).
% 0.20/0.43  fof(f201,plain,(
% 0.20/0.43    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_13),
% 0.20/0.43    inference(resolution,[],[f171,f78])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.20/0.43  fof(f171,plain,(
% 0.20/0.43    ~v3_pre_topc(k2_struct_0(sK0),sK0) | spl5_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f169])).
% 0.20/0.43  fof(f199,plain,(
% 0.20/0.43    spl5_17 | spl5_18),
% 0.20/0.43    inference(avatar_split_clause,[],[f191,f197,f194])).
% 0.20/0.43  fof(f191,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,sK2)) )),
% 0.20/0.43    inference(resolution,[],[f86,f91])).
% 0.20/0.43  fof(f178,plain,(
% 0.20/0.43    ~spl5_1 | ~spl5_14 | spl5_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f173,f130,f175,f103])).
% 0.20/0.43  fof(f173,plain,(
% 0.20/0.43    ~r2_hidden(k2_struct_0(sK0),sK2) | ~l1_struct_0(sK0) | spl5_6),
% 0.20/0.43    inference(superposition,[],[f132,f70])).
% 0.20/0.43  fof(f132,plain,(
% 0.20/0.43    ~r2_hidden(u1_struct_0(sK0),sK2) | spl5_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f130])).
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    spl5_1),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f111])).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    $false | spl5_1),
% 0.20/0.43    inference(resolution,[],[f105,f97])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    l1_struct_0(sK0)),
% 0.20/0.43    inference(resolution,[],[f71,f55])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.43  fof(f105,plain,(
% 0.20/0.43    ~l1_struct_0(sK0) | spl5_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f103])).
% 0.20/0.43  fof(f110,plain,(
% 0.20/0.43    ~spl5_1 | spl5_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f101,f107,f103])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    m1_subset_1(sK1,k2_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 0.20/0.43    inference(superposition,[],[f56,f70])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f48])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (25960)------------------------------
% 0.20/0.43  % (25960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (25960)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (25960)Memory used [KB]: 6396
% 0.20/0.43  % (25960)Time elapsed: 0.018 s
% 0.20/0.43  % (25960)------------------------------
% 0.20/0.43  % (25960)------------------------------
% 0.20/0.43  % (25953)Success in time 0.072 s
%------------------------------------------------------------------------------
