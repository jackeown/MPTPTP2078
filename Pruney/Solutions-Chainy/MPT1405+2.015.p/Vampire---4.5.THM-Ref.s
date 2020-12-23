%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 162 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  316 ( 540 expanded)
%              Number of equality atoms :   22 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f63,f67,f71,f78,f83,f124,f134,f138,f153,f158,f161])).

fof(f161,plain,
    ( ~ spl3_6
    | spl3_13 ),
    inference(avatar_split_clause,[],[f159,f156,f81])).

fof(f81,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f156,plain,
    ( spl3_13
  <=> r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f159,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_13 ),
    inference(resolution,[],[f157,f90])).

fof(f90,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f87,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f87,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f85,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f84,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f39,f38])).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X1)
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f53,f54])).

fof(f54,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f157,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f156])).

fof(f158,plain,
    ( ~ spl3_13
    | spl3_12 ),
    inference(avatar_split_clause,[],[f154,f151,f156])).

fof(f151,plain,
    ( spl3_12
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f154,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_12 ),
    inference(resolution,[],[f152,f55])).

fof(f55,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f152,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f153,plain,
    ( ~ spl3_4
    | ~ spl3_3
    | ~ spl3_12
    | spl3_9 ),
    inference(avatar_split_clause,[],[f144,f131,f151,f65,f69])).

fof(f69,plain,
    ( spl3_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f65,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f131,plain,
    ( spl3_9
  <=> r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f144,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_9 ),
    inference(superposition,[],[f132,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f132,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f131])).

fof(f138,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f129,f72])).

fof(f129,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_8
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f134,plain,
    ( ~ spl3_8
    | ~ spl3_9
    | ~ spl3_6
    | spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f125,f122,f57,f81,f131,f128])).

fof(f57,plain,
    ( spl3_1
  <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f122,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m2_connsp_2(X1,sK0,X0)
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f125,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_1
    | ~ spl3_7 ),
    inference(resolution,[],[f123,f58])).

fof(f58,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( m2_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f124,plain,
    ( ~ spl3_3
    | spl3_7
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f119,f76,f69,f122,f65])).

fof(f76,plain,
    ( spl3_5
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | ~ l1_pre_topc(sK0)
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f118,f77])).

fof(f77,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f117,f77])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f44,f70])).

fof(f70,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f83,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f79,f76,f61,f81])).

fof(f61,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f79,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(superposition,[],[f62,f77])).

fof(f62,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f78,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f74,f65,f76])).

fof(f74,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f73,f66])).

fof(f66,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f40,f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f71,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f67,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f65])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f35,f61])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f36,f57])).

fof(f36,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:39:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (7922)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.46  % (7942)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (7929)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (7935)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (7935)Refutation not found, incomplete strategy% (7935)------------------------------
% 0.22/0.47  % (7935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (7935)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (7935)Memory used [KB]: 1663
% 0.22/0.47  % (7935)Time elapsed: 0.004 s
% 0.22/0.47  % (7935)------------------------------
% 0.22/0.47  % (7935)------------------------------
% 0.22/0.48  % (7932)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % (7922)Refutation not found, incomplete strategy% (7922)------------------------------
% 0.22/0.48  % (7922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7922)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (7922)Memory used [KB]: 6268
% 0.22/0.48  % (7922)Time elapsed: 0.059 s
% 0.22/0.48  % (7922)------------------------------
% 0.22/0.48  % (7922)------------------------------
% 0.22/0.48  % (7942)Refutation not found, incomplete strategy% (7942)------------------------------
% 0.22/0.48  % (7942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7942)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (7942)Memory used [KB]: 10618
% 0.22/0.48  % (7942)Time elapsed: 0.063 s
% 0.22/0.48  % (7942)------------------------------
% 0.22/0.48  % (7942)------------------------------
% 0.22/0.48  % (7928)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (7934)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (7937)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (7928)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f59,f63,f67,f71,f78,f83,f124,f134,f138,f153,f158,f161])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    ~spl3_6 | spl3_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f159,f156,f81])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    spl3_13 <=> r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl3_13),
% 0.22/0.48    inference(resolution,[],[f157,f90])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ( ! [X2,X3] : (r2_hidden(X2,k1_zfmisc_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X3))) )),
% 0.22/0.48    inference(resolution,[],[f87,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | r2_hidden(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.48    inference(nnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(resolution,[],[f85,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(resolution,[],[f84,f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f39,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | ~r1_tarski(X2,X0)) )),
% 0.22/0.48    inference(resolution,[],[f53,f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.48    inference(rectify,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.48  fof(f157,plain,(
% 0.22/0.48    ~r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl3_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f156])).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    ~spl3_13 | spl3_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f154,f151,f156])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    spl3_12 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    ~r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl3_12),
% 0.22/0.48    inference(resolution,[],[f152,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(equality_resolution,[],[f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    ~r1_tarski(sK1,k2_struct_0(sK0)) | spl3_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f151])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    ~spl3_4 | ~spl3_3 | ~spl3_12 | spl3_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f144,f131,f151,f65,f69])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    spl3_4 <=> v2_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    spl3_3 <=> l1_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    spl3_9 <=> r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    ~r1_tarski(sK1,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl3_9),
% 0.22/0.48    inference(superposition,[],[f132,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    ~r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) | spl3_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f131])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    spl3_8),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f135])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    $false | spl3_8),
% 0.22/0.48    inference(resolution,[],[f129,f72])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f128])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    spl3_8 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    ~spl3_8 | ~spl3_9 | ~spl3_6 | spl3_1 | ~spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f125,f122,f57,f81,f131,f128])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    spl3_1 <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    spl3_7 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(X1,sK0,X0) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (spl3_1 | ~spl3_7)),
% 0.22/0.48    inference(resolution,[],[f123,f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f57])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m2_connsp_2(X1,sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f122])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    ~spl3_3 | spl3_7 | ~spl3_4 | ~spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f119,f76,f69,f122,f65])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    spl3_5 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~l1_pre_topc(sK0) | m2_connsp_2(X1,sK0,X0)) ) | (~spl3_4 | ~spl3_5)),
% 0.22/0.48    inference(forward_demodulation,[],[f118,f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f76])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | m2_connsp_2(X1,sK0,X0)) ) | (~spl3_4 | ~spl3_5)),
% 0.22/0.48    inference(forward_demodulation,[],[f117,f77])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | m2_connsp_2(X1,sK0,X0)) ) | ~spl3_4),
% 0.22/0.48    inference(resolution,[],[f44,f70])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    v2_pre_topc(sK0) | ~spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f69])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m2_connsp_2(X2,X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl3_6 | ~spl3_2 | ~spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f79,f76,f61,f81])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_2 | ~spl3_5)),
% 0.22/0.48    inference(superposition,[],[f62,f77])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f61])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl3_5 | ~spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f74,f65,f76])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_3),
% 0.22/0.48    inference(resolution,[],[f73,f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    l1_pre_topc(sK0) | ~spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f65])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.48    inference(resolution,[],[f40,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f33,f69])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    v2_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    (~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~m2_connsp_2(k2_struct_0(sK0),sK0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ? [X1] : (~m2_connsp_2(k2_struct_0(sK0),sK0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.48  fof(f12,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.22/0.48    inference(negated_conjecture,[],[f11])).
% 0.22/0.48  fof(f11,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f65])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f61])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ~spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f36,f57])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (7928)------------------------------
% 0.22/0.48  % (7928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7928)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (7928)Memory used [KB]: 10618
% 0.22/0.48  % (7928)Time elapsed: 0.068 s
% 0.22/0.48  % (7928)------------------------------
% 0.22/0.48  % (7928)------------------------------
% 0.22/0.48  % (7927)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (7921)Success in time 0.117 s
%------------------------------------------------------------------------------
