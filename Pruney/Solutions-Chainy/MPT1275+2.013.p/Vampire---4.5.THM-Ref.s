%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:44 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 350 expanded)
%              Number of leaves         :   39 ( 140 expanded)
%              Depth                    :   11
%              Number of atoms          :  569 (1305 expanded)
%              Number of equality atoms :   73 ( 193 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f728,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f94,f98,f102,f106,f223,f322,f419,f424,f441,f444,f451,f458,f471,f548,f567,f574,f588,f604,f611,f648,f694,f701,f723])).

fof(f723,plain,
    ( spl4_36
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f718,f692,f609])).

fof(f609,plain,
    ( spl4_36
  <=> r2_hidden(sK2(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f692,plain,
    ( spl4_45
  <=> r2_hidden(sK2(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f718,plain,
    ( r2_hidden(sK2(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl4_45 ),
    inference(resolution,[],[f693,f84])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f693,plain,
    ( r2_hidden(sK2(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f692])).

fof(f701,plain,
    ( spl4_21
    | ~ spl4_23
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f695,f564,f469,f456])).

fof(f456,plain,
    ( spl4_21
  <=> r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f469,plain,
    ( spl4_23
  <=> r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f564,plain,
    ( spl4_28
  <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f695,plain,
    ( r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),sK1)
    | ~ spl4_23
    | ~ spl4_28 ),
    inference(resolution,[],[f653,f470])).

fof(f470,plain,
    ( r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f469])).

fof(f653,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tops_1(sK0,sK1))
        | r2_hidden(X0,sK1) )
    | ~ spl4_28 ),
    inference(superposition,[],[f114,f565])).

fof(f565,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f564])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f84,f78])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f60,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f694,plain,
    ( ~ spl4_4
    | spl4_45
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f690,f646,f692,f100])).

fof(f100,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f646,plain,
    ( spl4_40
  <=> r2_hidden(sK2(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f690,plain,
    ( r2_hidden(sK2(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_40 ),
    inference(superposition,[],[f647,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f647,plain,
    ( r2_hidden(sK2(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f646])).

fof(f648,plain,
    ( spl4_40
    | spl4_32 ),
    inference(avatar_split_clause,[],[f640,f586,f646])).

fof(f586,plain,
    ( spl4_32
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f640,plain,
    ( r2_hidden(sK2(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1))
    | spl4_32 ),
    inference(resolution,[],[f593,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f593,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | r2_hidden(sK2(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),X0) )
    | spl4_32 ),
    inference(resolution,[],[f587,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r2_hidden(sK2(X0,X1),X2) ) ),
    inference(resolution,[],[f66,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f587,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl4_32 ),
    inference(avatar_component_clause,[],[f586])).

fof(f611,plain,
    ( ~ spl4_36
    | spl4_35 ),
    inference(avatar_split_clause,[],[f606,f602,f609])).

fof(f602,plain,
    ( spl4_35
  <=> r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f606,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl4_35 ),
    inference(resolution,[],[f603,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f603,plain,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f602])).

fof(f604,plain,
    ( ~ spl4_4
    | ~ spl4_35
    | spl4_32 ),
    inference(avatar_split_clause,[],[f596,f586,f602,f100])).

fof(f596,plain,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_32 ),
    inference(superposition,[],[f587,f61])).

fof(f588,plain,
    ( ~ spl4_32
    | spl4_29 ),
    inference(avatar_split_clause,[],[f583,f572,f586])).

fof(f572,plain,
    ( spl4_29
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f583,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl4_29 ),
    inference(resolution,[],[f573,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f573,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f572])).

fof(f574,plain,
    ( ~ spl4_5
    | ~ spl4_29
    | spl4_27 ),
    inference(avatar_split_clause,[],[f568,f561,f572,f104])).

fof(f104,plain,
    ( spl4_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f561,plain,
    ( spl4_27
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f568,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_27 ),
    inference(resolution,[],[f562,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f562,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_27 ),
    inference(avatar_component_clause,[],[f561])).

fof(f567,plain,
    ( ~ spl4_27
    | spl4_28
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f555,f546,f564,f561])).

fof(f546,plain,
    ( spl4_24
  <=> k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f555,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_24 ),
    inference(superposition,[],[f79,f547])).

fof(f547,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f546])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f71,f59])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f548,plain,
    ( spl4_24
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f544,f220,f104,f100,f546])).

fof(f220,plain,
    ( spl4_11
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f544,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f541,f221])).

fof(f221,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f220])).

fof(f541,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f540,f101])).

fof(f101,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f540,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl4_5 ),
    inference(resolution,[],[f53,f105])).

fof(f105,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

fof(f471,plain,
    ( spl4_23
    | spl4_20 ),
    inference(avatar_split_clause,[],[f464,f449,f469])).

fof(f449,plain,
    ( spl4_20
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f464,plain,
    ( r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | spl4_20 ),
    inference(resolution,[],[f452,f80])).

fof(f452,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_tops_1(sK0,sK1),X0)
        | r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),X0) )
    | spl4_20 ),
    inference(resolution,[],[f450,f112])).

fof(f450,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f449])).

fof(f458,plain,
    ( ~ spl4_21
    | spl4_20 ),
    inference(avatar_split_clause,[],[f453,f449,f456])).

fof(f453,plain,
    ( ~ r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),sK1)
    | spl4_20 ),
    inference(resolution,[],[f450,f68])).

fof(f451,plain,
    ( ~ spl4_20
    | spl4_2
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f447,f434,f89,f449])).

fof(f89,plain,
    ( spl4_2
  <=> sK1 = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f434,plain,
    ( spl4_19
  <=> r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f447,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl4_19 ),
    inference(resolution,[],[f443,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f443,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f434])).

fof(f444,plain,
    ( ~ spl4_5
    | ~ spl4_4
    | spl4_19
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f442,f320,f434,f100,f104])).

fof(f320,plain,
    ( spl4_15
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f442,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_15 ),
    inference(resolution,[],[f440,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

fof(f440,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f320])).

fof(f441,plain,
    ( ~ spl4_5
    | ~ spl4_4
    | spl4_15
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f438,f220,f86,f320,f100,f104])).

fof(f86,plain,
    ( spl4_1
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f438,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f437,f221])).

fof(f437,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f92,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v3_tops_1(X1,X0)
      | v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

fof(f92,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f424,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | spl4_16 ),
    inference(resolution,[],[f418,f80])).

fof(f418,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl4_16
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f419,plain,
    ( ~ spl4_4
    | ~ spl4_16
    | ~ spl4_2
    | ~ spl4_5
    | spl4_15 ),
    inference(avatar_split_clause,[],[f415,f320,f104,f89,f417,f100])).

fof(f415,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_5
    | spl4_15 ),
    inference(forward_demodulation,[],[f412,f93])).

fof(f93,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f412,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_5
    | spl4_15 ),
    inference(resolution,[],[f410,f321])).

fof(f321,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f320])).

fof(f410,plain,
    ( ! [X0] :
        ( v2_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k2_tops_1(sK0,X0)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f58,f105])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f322,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_15
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f318,f220,f104,f320,f100,f86])).

fof(f318,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_1(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(superposition,[],[f317,f221])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ v2_tops_1(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tops_1(X0,sK0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f56,f105])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f223,plain,
    ( spl4_11
    | ~ spl4_4
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f218,f104,f96,f100,f220])).

fof(f96,plain,
    ( spl4_3
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f218,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(resolution,[],[f217,f97])).

fof(f97,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl4_5 ),
    inference(resolution,[],[f54,f105])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f106,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f48,f104])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( sK1 != k2_tops_1(sK0,sK1)
      | ~ v3_tops_1(sK1,sK0) )
    & ( sK1 = k2_tops_1(sK0,sK1)
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != X1
          | ~ v3_tops_1(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = X1
          | v3_tops_1(X1,sK0) )
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( sK1 != k2_tops_1(sK0,sK1)
        | ~ v3_tops_1(sK1,sK0) )
      & ( sK1 = k2_tops_1(sK0,sK1)
        | v3_tops_1(sK1,sK0) )
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

fof(f102,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f49,f100])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f50,f96])).

fof(f50,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f51,f89,f86])).

fof(f51,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f52,f89,f86])).

fof(f52,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:39:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (9784)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.48  % (9792)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (9783)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (9773)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (9774)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (9788)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (9776)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (9775)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (9782)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (9782)Refutation not found, incomplete strategy% (9782)------------------------------
% 0.21/0.56  % (9782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9782)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9782)Memory used [KB]: 10618
% 0.21/0.56  % (9782)Time elapsed: 0.155 s
% 0.21/0.56  % (9782)------------------------------
% 0.21/0.56  % (9782)------------------------------
% 0.21/0.56  % (9796)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (9800)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.57  % (9780)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.47/0.57  % (9789)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.57  % (9772)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.47/0.57  % (9797)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.47/0.57  % (9790)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.47/0.57  % (9773)Refutation not found, incomplete strategy% (9773)------------------------------
% 1.47/0.57  % (9773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (9773)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (9773)Memory used [KB]: 10746
% 1.47/0.57  % (9773)Time elapsed: 0.147 s
% 1.47/0.57  % (9773)------------------------------
% 1.47/0.57  % (9773)------------------------------
% 1.47/0.57  % (9791)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.47/0.58  % (9788)Refutation not found, incomplete strategy% (9788)------------------------------
% 1.47/0.58  % (9788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  % (9788)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.58  
% 1.47/0.58  % (9788)Memory used [KB]: 10618
% 1.47/0.58  % (9788)Time elapsed: 0.169 s
% 1.47/0.58  % (9788)------------------------------
% 1.47/0.58  % (9788)------------------------------
% 1.47/0.58  % (9781)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.58  % (9781)Refutation not found, incomplete strategy% (9781)------------------------------
% 1.47/0.58  % (9781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  % (9781)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.58  
% 1.47/0.58  % (9781)Memory used [KB]: 10618
% 1.47/0.58  % (9781)Time elapsed: 0.162 s
% 1.47/0.58  % (9781)------------------------------
% 1.47/0.58  % (9781)------------------------------
% 1.47/0.58  % (9799)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.47/0.58  % (9795)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.78/0.59  % (9786)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.78/0.59  % (9793)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.78/0.59  % (9787)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.78/0.59  % (9785)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.78/0.59  % (9771)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.78/0.60  % (9778)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.78/0.60  % (9779)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.78/0.60  % (9777)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.78/0.60  % (9779)Refutation not found, incomplete strategy% (9779)------------------------------
% 1.78/0.60  % (9779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (9779)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.60  
% 1.78/0.60  % (9779)Memory used [KB]: 10746
% 1.78/0.60  % (9779)Time elapsed: 0.175 s
% 1.78/0.60  % (9779)------------------------------
% 1.78/0.60  % (9779)------------------------------
% 1.78/0.60  % (9794)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.78/0.60  % (9793)Refutation not found, incomplete strategy% (9793)------------------------------
% 1.78/0.60  % (9793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (9793)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.60  
% 1.78/0.60  % (9793)Memory used [KB]: 10874
% 1.78/0.60  % (9793)Time elapsed: 0.115 s
% 1.78/0.60  % (9793)------------------------------
% 1.78/0.60  % (9793)------------------------------
% 1.78/0.61  % (9798)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.22/0.65  % (9790)Refutation found. Thanks to Tanya!
% 2.22/0.65  % SZS status Theorem for theBenchmark
% 2.22/0.65  % SZS output start Proof for theBenchmark
% 2.22/0.65  fof(f728,plain,(
% 2.22/0.65    $false),
% 2.22/0.65    inference(avatar_sat_refutation,[],[f91,f94,f98,f102,f106,f223,f322,f419,f424,f441,f444,f451,f458,f471,f548,f567,f574,f588,f604,f611,f648,f694,f701,f723])).
% 2.22/0.65  fof(f723,plain,(
% 2.22/0.65    spl4_36 | ~spl4_45),
% 2.22/0.65    inference(avatar_split_clause,[],[f718,f692,f609])).
% 2.22/0.65  fof(f609,plain,(
% 2.22/0.65    spl4_36 <=> r2_hidden(sK2(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),u1_struct_0(sK0))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 2.22/0.65  fof(f692,plain,(
% 2.22/0.65    spl4_45 <=> r2_hidden(sK2(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 2.22/0.65  fof(f718,plain,(
% 2.22/0.65    r2_hidden(sK2(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl4_45),
% 2.22/0.65    inference(resolution,[],[f693,f84])).
% 2.22/0.65  fof(f84,plain,(
% 2.22/0.65    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 2.22/0.65    inference(equality_resolution,[],[f72])).
% 2.22/0.65  fof(f72,plain,(
% 2.22/0.65    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.22/0.65    inference(cnf_transformation,[],[f47])).
% 2.22/0.65  fof(f47,plain,(
% 2.22/0.65    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).
% 2.22/0.65  fof(f46,plain,(
% 2.22/0.65    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f45,plain,(
% 2.22/0.65    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.22/0.65    inference(rectify,[],[f44])).
% 2.22/0.65  fof(f44,plain,(
% 2.22/0.65    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.22/0.65    inference(flattening,[],[f43])).
% 2.22/0.65  fof(f43,plain,(
% 2.22/0.65    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.22/0.65    inference(nnf_transformation,[],[f2])).
% 2.22/0.65  fof(f2,axiom,(
% 2.22/0.65    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.22/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.22/0.65  fof(f693,plain,(
% 2.22/0.65    r2_hidden(sK2(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl4_45),
% 2.22/0.65    inference(avatar_component_clause,[],[f692])).
% 2.22/0.65  fof(f701,plain,(
% 2.22/0.65    spl4_21 | ~spl4_23 | ~spl4_28),
% 2.22/0.65    inference(avatar_split_clause,[],[f695,f564,f469,f456])).
% 2.22/0.65  fof(f456,plain,(
% 2.22/0.65    spl4_21 <=> r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),sK1)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.22/0.65  fof(f469,plain,(
% 2.22/0.65    spl4_23 <=> r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 2.22/0.65  fof(f564,plain,(
% 2.22/0.65    spl4_28 <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 2.22/0.65  fof(f695,plain,(
% 2.22/0.65    r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),sK1) | (~spl4_23 | ~spl4_28)),
% 2.22/0.65    inference(resolution,[],[f653,f470])).
% 2.22/0.65  fof(f470,plain,(
% 2.22/0.65    r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | ~spl4_23),
% 2.22/0.65    inference(avatar_component_clause,[],[f469])).
% 2.22/0.65  fof(f653,plain,(
% 2.22/0.65    ( ! [X0] : (~r2_hidden(X0,k2_tops_1(sK0,sK1)) | r2_hidden(X0,sK1)) ) | ~spl4_28),
% 2.22/0.65    inference(superposition,[],[f114,f565])).
% 2.22/0.65  fof(f565,plain,(
% 2.22/0.65    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl4_28),
% 2.22/0.65    inference(avatar_component_clause,[],[f564])).
% 2.22/0.65  fof(f114,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | r2_hidden(X2,X0)) )),
% 2.22/0.65    inference(superposition,[],[f84,f78])).
% 2.22/0.65  fof(f78,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.22/0.65    inference(definition_unfolding,[],[f60,f59])).
% 2.22/0.65  fof(f59,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f7])).
% 2.22/0.65  fof(f7,axiom,(
% 2.22/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.22/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.22/0.65  fof(f60,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f4])).
% 2.22/0.65  fof(f4,axiom,(
% 2.22/0.65    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.22/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.22/0.65  fof(f694,plain,(
% 2.22/0.65    ~spl4_4 | spl4_45 | ~spl4_40),
% 2.22/0.65    inference(avatar_split_clause,[],[f690,f646,f692,f100])).
% 2.22/0.65  fof(f100,plain,(
% 2.22/0.65    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.22/0.65  fof(f646,plain,(
% 2.22/0.65    spl4_40 <=> r2_hidden(sK2(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 2.22/0.65  fof(f690,plain,(
% 2.22/0.65    r2_hidden(sK2(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_40),
% 2.22/0.65    inference(superposition,[],[f647,f61])).
% 2.22/0.65  fof(f61,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f24])).
% 2.22/0.65  fof(f24,plain,(
% 2.22/0.65    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f5])).
% 2.22/0.65  fof(f5,axiom,(
% 2.22/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.22/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.22/0.65  fof(f647,plain,(
% 2.22/0.65    r2_hidden(sK2(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl4_40),
% 2.22/0.65    inference(avatar_component_clause,[],[f646])).
% 2.22/0.65  fof(f648,plain,(
% 2.22/0.65    spl4_40 | spl4_32),
% 2.22/0.65    inference(avatar_split_clause,[],[f640,f586,f646])).
% 2.22/0.65  fof(f586,plain,(
% 2.22/0.65    spl4_32 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 2.22/0.65  fof(f640,plain,(
% 2.22/0.65    r2_hidden(sK2(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1)) | spl4_32),
% 2.22/0.65    inference(resolution,[],[f593,f80])).
% 2.22/0.65  fof(f80,plain,(
% 2.22/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.22/0.65    inference(equality_resolution,[],[f64])).
% 2.22/0.65  fof(f64,plain,(
% 2.22/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.22/0.65    inference(cnf_transformation,[],[f37])).
% 2.22/0.65  fof(f37,plain,(
% 2.22/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.65    inference(flattening,[],[f36])).
% 2.22/0.65  fof(f36,plain,(
% 2.22/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.65    inference(nnf_transformation,[],[f3])).
% 2.22/0.65  fof(f3,axiom,(
% 2.22/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.22/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.22/0.65  fof(f593,plain,(
% 2.22/0.65    ( ! [X0] : (~r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X0) | r2_hidden(sK2(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),X0)) ) | spl4_32),
% 2.22/0.65    inference(resolution,[],[f587,f112])).
% 2.22/0.65  fof(f112,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r2_hidden(sK2(X0,X1),X2)) )),
% 2.22/0.65    inference(resolution,[],[f66,f67])).
% 2.22/0.65  fof(f67,plain,(
% 2.22/0.65    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f41])).
% 2.22/0.65  fof(f41,plain,(
% 2.22/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 2.22/0.65  fof(f40,plain,(
% 2.22/0.65    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f39,plain,(
% 2.22/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.22/0.65    inference(rectify,[],[f38])).
% 2.22/0.65  fof(f38,plain,(
% 2.22/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.22/0.65    inference(nnf_transformation,[],[f27])).
% 2.22/0.65  fof(f27,plain,(
% 2.22/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f1])).
% 2.22/0.65  fof(f1,axiom,(
% 2.22/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.22/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.22/0.65  fof(f66,plain,(
% 2.22/0.65    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f41])).
% 2.22/0.65  fof(f587,plain,(
% 2.22/0.65    ~r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl4_32),
% 2.22/0.65    inference(avatar_component_clause,[],[f586])).
% 2.22/0.65  fof(f611,plain,(
% 2.22/0.65    ~spl4_36 | spl4_35),
% 2.22/0.65    inference(avatar_split_clause,[],[f606,f602,f609])).
% 2.22/0.65  fof(f602,plain,(
% 2.22/0.65    spl4_35 <=> r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 2.22/0.65  fof(f606,plain,(
% 2.22/0.65    ~r2_hidden(sK2(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),u1_struct_0(sK0)) | spl4_35),
% 2.22/0.65    inference(resolution,[],[f603,f68])).
% 2.22/0.65  fof(f68,plain,(
% 2.22/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f41])).
% 2.22/0.65  fof(f603,plain,(
% 2.22/0.65    ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl4_35),
% 2.22/0.65    inference(avatar_component_clause,[],[f602])).
% 2.22/0.65  fof(f604,plain,(
% 2.22/0.65    ~spl4_4 | ~spl4_35 | spl4_32),
% 2.22/0.65    inference(avatar_split_clause,[],[f596,f586,f602,f100])).
% 2.22/0.65  fof(f596,plain,(
% 2.22/0.65    ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_32),
% 2.22/0.65    inference(superposition,[],[f587,f61])).
% 2.22/0.65  fof(f588,plain,(
% 2.22/0.65    ~spl4_32 | spl4_29),
% 2.22/0.65    inference(avatar_split_clause,[],[f583,f572,f586])).
% 2.22/0.65  fof(f572,plain,(
% 2.22/0.65    spl4_29 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.22/0.65  fof(f583,plain,(
% 2.22/0.65    ~r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl4_29),
% 2.22/0.65    inference(resolution,[],[f573,f70])).
% 2.22/0.65  fof(f70,plain,(
% 2.22/0.65    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f42])).
% 2.22/0.65  fof(f42,plain,(
% 2.22/0.65    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.22/0.65    inference(nnf_transformation,[],[f8])).
% 2.22/0.65  fof(f8,axiom,(
% 2.22/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.22/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.22/0.65  fof(f573,plain,(
% 2.22/0.65    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_29),
% 2.22/0.65    inference(avatar_component_clause,[],[f572])).
% 2.22/0.65  fof(f574,plain,(
% 2.22/0.65    ~spl4_5 | ~spl4_29 | spl4_27),
% 2.22/0.65    inference(avatar_split_clause,[],[f568,f561,f572,f104])).
% 2.22/0.65  fof(f104,plain,(
% 2.22/0.65    spl4_5 <=> l1_pre_topc(sK0)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.22/0.65  fof(f561,plain,(
% 2.22/0.65    spl4_27 <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.22/0.65  fof(f568,plain,(
% 2.22/0.65    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_27),
% 2.22/0.65    inference(resolution,[],[f562,f62])).
% 2.22/0.65  fof(f62,plain,(
% 2.22/0.65    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f26])).
% 2.22/0.65  fof(f26,plain,(
% 2.22/0.65    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.22/0.65    inference(flattening,[],[f25])).
% 2.22/0.65  fof(f25,plain,(
% 2.22/0.65    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f9])).
% 2.22/0.65  fof(f9,axiom,(
% 2.22/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.22/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.22/0.65  fof(f562,plain,(
% 2.22/0.65    ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_27),
% 2.22/0.65    inference(avatar_component_clause,[],[f561])).
% 2.22/0.65  fof(f567,plain,(
% 2.22/0.65    ~spl4_27 | spl4_28 | ~spl4_24),
% 2.22/0.65    inference(avatar_split_clause,[],[f555,f546,f564,f561])).
% 2.22/0.65  fof(f546,plain,(
% 2.22/0.65    spl4_24 <=> k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.22/0.65  fof(f555,plain,(
% 2.22/0.65    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_24),
% 2.22/0.65    inference(superposition,[],[f79,f547])).
% 2.22/0.65  fof(f547,plain,(
% 2.22/0.65    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl4_24),
% 2.22/0.65    inference(avatar_component_clause,[],[f546])).
% 2.22/0.65  fof(f79,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.22/0.65    inference(definition_unfolding,[],[f71,f59])).
% 2.22/0.65  fof(f71,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f28])).
% 2.22/0.65  fof(f28,plain,(
% 2.22/0.65    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f6])).
% 2.22/0.65  fof(f6,axiom,(
% 2.22/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.22/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.22/0.65  fof(f548,plain,(
% 2.22/0.65    spl4_24 | ~spl4_4 | ~spl4_5 | ~spl4_11),
% 2.22/0.65    inference(avatar_split_clause,[],[f544,f220,f104,f100,f546])).
% 2.22/0.65  fof(f220,plain,(
% 2.22/0.65    spl4_11 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.22/0.65  fof(f544,plain,(
% 2.22/0.65    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl4_4 | ~spl4_5 | ~spl4_11)),
% 2.22/0.65    inference(forward_demodulation,[],[f541,f221])).
% 2.22/0.65  fof(f221,plain,(
% 2.22/0.65    sK1 = k2_pre_topc(sK0,sK1) | ~spl4_11),
% 2.22/0.65    inference(avatar_component_clause,[],[f220])).
% 2.22/0.65  fof(f541,plain,(
% 2.22/0.65    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl4_4 | ~spl4_5)),
% 2.22/0.65    inference(resolution,[],[f540,f101])).
% 2.22/0.65  fof(f101,plain,(
% 2.22/0.65    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_4),
% 2.22/0.65    inference(avatar_component_clause,[],[f100])).
% 2.22/0.65  fof(f540,plain,(
% 2.22/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl4_5),
% 2.22/0.65    inference(resolution,[],[f53,f105])).
% 2.22/0.65  fof(f105,plain,(
% 2.22/0.65    l1_pre_topc(sK0) | ~spl4_5),
% 2.22/0.65    inference(avatar_component_clause,[],[f104])).
% 2.22/0.65  fof(f53,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f19])).
% 2.22/0.65  fof(f19,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.65    inference(ennf_transformation,[],[f11])).
% 2.22/0.65  fof(f11,axiom,(
% 2.22/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 2.22/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).
% 2.22/0.65  fof(f471,plain,(
% 2.22/0.65    spl4_23 | spl4_20),
% 2.22/0.65    inference(avatar_split_clause,[],[f464,f449,f469])).
% 2.22/0.65  fof(f449,plain,(
% 2.22/0.65    spl4_20 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.22/0.65  fof(f464,plain,(
% 2.22/0.65    r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | spl4_20),
% 2.22/0.65    inference(resolution,[],[f452,f80])).
% 2.22/0.65  fof(f452,plain,(
% 2.22/0.65    ( ! [X0] : (~r1_tarski(k2_tops_1(sK0,sK1),X0) | r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),X0)) ) | spl4_20),
% 2.22/0.65    inference(resolution,[],[f450,f112])).
% 2.22/0.65  fof(f450,plain,(
% 2.22/0.65    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl4_20),
% 2.22/0.65    inference(avatar_component_clause,[],[f449])).
% 2.22/0.65  fof(f458,plain,(
% 2.22/0.65    ~spl4_21 | spl4_20),
% 2.22/0.65    inference(avatar_split_clause,[],[f453,f449,f456])).
% 2.22/0.65  fof(f453,plain,(
% 2.22/0.65    ~r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),sK1) | spl4_20),
% 2.22/0.65    inference(resolution,[],[f450,f68])).
% 2.22/0.65  fof(f451,plain,(
% 2.22/0.65    ~spl4_20 | spl4_2 | ~spl4_19),
% 2.22/0.65    inference(avatar_split_clause,[],[f447,f434,f89,f449])).
% 2.22/0.65  fof(f89,plain,(
% 2.22/0.65    spl4_2 <=> sK1 = k2_tops_1(sK0,sK1)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.22/0.65  fof(f434,plain,(
% 2.22/0.65    spl4_19 <=> r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.22/0.65  fof(f447,plain,(
% 2.22/0.65    sK1 = k2_tops_1(sK0,sK1) | ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl4_19),
% 2.22/0.65    inference(resolution,[],[f443,f65])).
% 2.22/0.65  fof(f65,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f37])).
% 2.22/0.65  fof(f443,plain,(
% 2.22/0.65    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~spl4_19),
% 2.22/0.65    inference(avatar_component_clause,[],[f434])).
% 2.22/0.65  fof(f444,plain,(
% 2.22/0.65    ~spl4_5 | ~spl4_4 | spl4_19 | ~spl4_15),
% 2.22/0.65    inference(avatar_split_clause,[],[f442,f320,f434,f100,f104])).
% 2.22/0.65  fof(f320,plain,(
% 2.22/0.65    spl4_15 <=> v2_tops_1(sK1,sK0)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.22/0.65  fof(f442,plain,(
% 2.22/0.65    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_15),
% 2.22/0.65    inference(resolution,[],[f440,f57])).
% 2.22/0.65  fof(f57,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f35])).
% 2.22/0.65  fof(f35,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.65    inference(nnf_transformation,[],[f23])).
% 2.22/0.65  fof(f23,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.65    inference(ennf_transformation,[],[f13])).
% 2.22/0.65  fof(f13,axiom,(
% 2.22/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 2.22/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).
% 2.22/0.65  fof(f440,plain,(
% 2.22/0.65    v2_tops_1(sK1,sK0) | ~spl4_15),
% 2.22/0.65    inference(avatar_component_clause,[],[f320])).
% 2.22/0.65  fof(f441,plain,(
% 2.22/0.65    ~spl4_5 | ~spl4_4 | spl4_15 | ~spl4_1 | ~spl4_11),
% 2.22/0.65    inference(avatar_split_clause,[],[f438,f220,f86,f320,f100,f104])).
% 2.22/0.65  fof(f86,plain,(
% 2.22/0.65    spl4_1 <=> v3_tops_1(sK1,sK0)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.22/0.65  fof(f438,plain,(
% 2.22/0.65    v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_1 | ~spl4_11)),
% 2.22/0.65    inference(forward_demodulation,[],[f437,f221])).
% 2.22/0.65  fof(f437,plain,(
% 2.22/0.65    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_1),
% 2.22/0.65    inference(resolution,[],[f92,f55])).
% 2.22/0.65  fof(f55,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~v3_tops_1(X1,X0) | v2_tops_1(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f34])).
% 2.22/0.65  fof(f34,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.65    inference(nnf_transformation,[],[f22])).
% 2.22/0.65  fof(f22,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.65    inference(ennf_transformation,[],[f12])).
% 2.22/0.65  fof(f12,axiom,(
% 2.22/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 2.22/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).
% 2.22/0.65  fof(f92,plain,(
% 2.22/0.65    v3_tops_1(sK1,sK0) | ~spl4_1),
% 2.22/0.65    inference(avatar_component_clause,[],[f86])).
% 2.22/0.65  fof(f424,plain,(
% 2.22/0.65    spl4_16),
% 2.22/0.65    inference(avatar_contradiction_clause,[],[f420])).
% 2.22/0.65  fof(f420,plain,(
% 2.22/0.65    $false | spl4_16),
% 2.22/0.65    inference(resolution,[],[f418,f80])).
% 2.22/0.65  fof(f418,plain,(
% 2.22/0.65    ~r1_tarski(sK1,sK1) | spl4_16),
% 2.22/0.65    inference(avatar_component_clause,[],[f417])).
% 2.22/0.65  fof(f417,plain,(
% 2.22/0.65    spl4_16 <=> r1_tarski(sK1,sK1)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.22/0.65  fof(f419,plain,(
% 2.22/0.65    ~spl4_4 | ~spl4_16 | ~spl4_2 | ~spl4_5 | spl4_15),
% 2.22/0.65    inference(avatar_split_clause,[],[f415,f320,f104,f89,f417,f100])).
% 2.22/0.65  fof(f415,plain,(
% 2.22/0.65    ~r1_tarski(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_5 | spl4_15)),
% 2.22/0.65    inference(forward_demodulation,[],[f412,f93])).
% 2.22/0.65  fof(f93,plain,(
% 2.22/0.65    sK1 = k2_tops_1(sK0,sK1) | ~spl4_2),
% 2.22/0.65    inference(avatar_component_clause,[],[f89])).
% 2.22/0.65  fof(f412,plain,(
% 2.22/0.65    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | (~spl4_5 | spl4_15)),
% 2.22/0.65    inference(resolution,[],[f410,f321])).
% 2.22/0.65  fof(f321,plain,(
% 2.22/0.65    ~v2_tops_1(sK1,sK0) | spl4_15),
% 2.22/0.65    inference(avatar_component_clause,[],[f320])).
% 2.22/0.65  fof(f410,plain,(
% 2.22/0.65    ( ! [X0] : (v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k2_tops_1(sK0,X0))) ) | ~spl4_5),
% 2.22/0.65    inference(resolution,[],[f58,f105])).
% 2.22/0.65  fof(f58,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f35])).
% 2.22/0.65  fof(f322,plain,(
% 2.22/0.65    spl4_1 | ~spl4_4 | ~spl4_15 | ~spl4_5 | ~spl4_11),
% 2.22/0.65    inference(avatar_split_clause,[],[f318,f220,f104,f320,f100,f86])).
% 2.22/0.65  fof(f318,plain,(
% 2.22/0.65    ~v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_1(sK1,sK0) | (~spl4_5 | ~spl4_11)),
% 2.22/0.65    inference(superposition,[],[f317,f221])).
% 2.22/0.65  fof(f317,plain,(
% 2.22/0.65    ( ! [X0] : (~v2_tops_1(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_1(X0,sK0)) ) | ~spl4_5),
% 2.22/0.65    inference(resolution,[],[f56,f105])).
% 2.22/0.65  fof(f56,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tops_1(X1,X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f34])).
% 2.22/0.65  fof(f223,plain,(
% 2.22/0.65    spl4_11 | ~spl4_4 | ~spl4_3 | ~spl4_5),
% 2.22/0.65    inference(avatar_split_clause,[],[f218,f104,f96,f100,f220])).
% 2.22/0.65  fof(f96,plain,(
% 2.22/0.65    spl4_3 <=> v4_pre_topc(sK1,sK0)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.22/0.65  fof(f218,plain,(
% 2.22/0.65    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | (~spl4_3 | ~spl4_5)),
% 2.22/0.65    inference(resolution,[],[f217,f97])).
% 2.22/0.65  fof(f97,plain,(
% 2.22/0.65    v4_pre_topc(sK1,sK0) | ~spl4_3),
% 2.22/0.65    inference(avatar_component_clause,[],[f96])).
% 2.22/0.65  fof(f217,plain,(
% 2.22/0.65    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl4_5),
% 2.22/0.65    inference(resolution,[],[f54,f105])).
% 2.22/0.65  fof(f54,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 2.22/0.65    inference(cnf_transformation,[],[f21])).
% 2.22/0.65  fof(f21,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.65    inference(flattening,[],[f20])).
% 2.22/0.65  fof(f20,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.65    inference(ennf_transformation,[],[f16])).
% 2.22/0.65  fof(f16,plain,(
% 2.22/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 2.22/0.65    inference(pure_predicate_removal,[],[f10])).
% 2.22/0.65  fof(f10,axiom,(
% 2.22/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.22/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.22/0.65  fof(f106,plain,(
% 2.22/0.65    spl4_5),
% 2.22/0.65    inference(avatar_split_clause,[],[f48,f104])).
% 2.22/0.65  fof(f48,plain,(
% 2.22/0.65    l1_pre_topc(sK0)),
% 2.22/0.65    inference(cnf_transformation,[],[f33])).
% 2.22/0.65  fof(f33,plain,(
% 2.22/0.65    ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 2.22/0.65  fof(f31,plain,(
% 2.22/0.65    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f32,plain,(
% 2.22/0.65    ? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f30,plain,(
% 2.22/0.65    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.22/0.65    inference(flattening,[],[f29])).
% 2.22/0.65  fof(f29,plain,(
% 2.22/0.65    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.22/0.65    inference(nnf_transformation,[],[f18])).
% 2.22/0.65  fof(f18,plain,(
% 2.22/0.65    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.22/0.65    inference(flattening,[],[f17])).
% 2.22/0.65  fof(f17,plain,(
% 2.22/0.65    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.22/0.65    inference(ennf_transformation,[],[f15])).
% 2.22/0.65  fof(f15,negated_conjecture,(
% 2.22/0.65    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 2.22/0.65    inference(negated_conjecture,[],[f14])).
% 2.22/0.65  fof(f14,conjecture,(
% 2.22/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 2.22/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).
% 2.22/0.65  fof(f102,plain,(
% 2.22/0.65    spl4_4),
% 2.22/0.65    inference(avatar_split_clause,[],[f49,f100])).
% 2.22/0.65  fof(f49,plain,(
% 2.22/0.65    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.65    inference(cnf_transformation,[],[f33])).
% 2.22/0.65  fof(f98,plain,(
% 2.22/0.65    spl4_3),
% 2.22/0.65    inference(avatar_split_clause,[],[f50,f96])).
% 2.22/0.65  fof(f50,plain,(
% 2.22/0.65    v4_pre_topc(sK1,sK0)),
% 2.22/0.65    inference(cnf_transformation,[],[f33])).
% 2.22/0.65  fof(f94,plain,(
% 2.22/0.65    spl4_1 | spl4_2),
% 2.22/0.65    inference(avatar_split_clause,[],[f51,f89,f86])).
% 2.22/0.65  fof(f51,plain,(
% 2.22/0.65    sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)),
% 2.22/0.65    inference(cnf_transformation,[],[f33])).
% 2.22/0.65  fof(f91,plain,(
% 2.22/0.65    ~spl4_1 | ~spl4_2),
% 2.22/0.65    inference(avatar_split_clause,[],[f52,f89,f86])).
% 2.22/0.65  fof(f52,plain,(
% 2.22/0.65    sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)),
% 2.22/0.65    inference(cnf_transformation,[],[f33])).
% 2.22/0.65  % SZS output end Proof for theBenchmark
% 2.22/0.65  % (9790)------------------------------
% 2.22/0.65  % (9790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.65  % (9790)Termination reason: Refutation
% 2.22/0.65  
% 2.22/0.65  % (9790)Memory used [KB]: 11129
% 2.22/0.65  % (9790)Time elapsed: 0.255 s
% 2.22/0.65  % (9790)------------------------------
% 2.22/0.65  % (9790)------------------------------
% 2.22/0.66  % (9770)Success in time 0.294 s
%------------------------------------------------------------------------------
