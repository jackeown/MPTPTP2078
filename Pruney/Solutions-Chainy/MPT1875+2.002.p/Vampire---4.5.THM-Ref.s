%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 627 expanded)
%              Number of leaves         :   29 ( 197 expanded)
%              Depth                    :   17
%              Number of atoms          :  629 (3277 expanded)
%              Number of equality atoms :   54 ( 105 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f588,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f174,f247,f258,f280,f313,f498,f506,f509,f586])).

fof(f586,plain,
    ( ~ spl6_5
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f585])).

fof(f585,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f548,f158])).

fof(f158,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,X0) = X0 ),
    inference(resolution,[],[f120,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0)
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(general_splitting,[],[f104,f109_D])).

fof(f109,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | sP5(X0) ) ),
    inference(cnf_transformation,[],[f109_D])).

fof(f109_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    <=> ~ sP5(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f120,plain,(
    sP5(u1_struct_0(sK0)) ),
    inference(resolution,[],[f72,f109])).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f548,plain,
    ( sK1 != k9_subset_1(u1_struct_0(sK0),sK1,sK1)
    | ~ spl6_5
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f434,f173])).

fof(f173,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl6_5
  <=> sK1 = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f434,plain,
    ( sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK0,sK1))
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f433,f68])).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f433,plain,
    ( sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f432,f69])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f432,plain,
    ( sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f431,f71])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f431,plain,
    ( sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f430,f72])).

fof(f430,plain,
    ( sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f429,f73])).

fof(f73,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f429,plain,
    ( sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK0,sK1))
    | v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_14 ),
    inference(superposition,[],[f86,f275])).

fof(f275,plain,
    ( sK2(sK0,sK1) = k2_pre_topc(sK0,sK2(sK0,sK1))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl6_14
  <=> sK2(sK0,sK1) = k2_pre_topc(sK0,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f86,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1)))
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1)))
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1)))
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(f509,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | ~ spl6_3
    | spl6_4 ),
    inference(subsumption_resolution,[],[f334,f152])).

fof(f152,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl6_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f334,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_4 ),
    inference(resolution,[],[f189,f91])).

fof(f91,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f189,plain,
    ( r2_hidden(sK4(sK1,sK2(sK0,sK1)),sK1)
    | spl6_4 ),
    inference(resolution,[],[f169,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f65,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f169,plain,
    ( ~ r1_tarski(sK1,sK2(sK0,sK1))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl6_4
  <=> r1_tarski(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f506,plain,
    ( ~ spl6_3
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f505])).

fof(f505,plain,
    ( $false
    | ~ spl6_3
    | spl6_19 ),
    inference(subsumption_resolution,[],[f152,f485])).

fof(f485,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_19 ),
    inference(resolution,[],[f480,f91])).

fof(f480,plain,
    ( r2_hidden(sK3(sK2(sK0,sK1)),sK1)
    | spl6_19 ),
    inference(resolution,[],[f469,f164])).

fof(f164,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2(sK0,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f147,f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f147,plain,(
    r1_tarski(sK2(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f146,f68])).

fof(f146,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f145,f69])).

fof(f145,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f144,f71])).

fof(f144,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f117,f73])).

fof(f117,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f72,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f469,plain,
    ( r2_hidden(sK3(sK2(sK0,sK1)),sK2(sK0,sK1))
    | spl6_19 ),
    inference(resolution,[],[f312,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f312,plain,
    ( ~ v1_xboole_0(sK2(sK0,sK1))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl6_19
  <=> v1_xboole_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f498,plain,(
    ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f497])).

fof(f497,plain,
    ( $false
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f496,f73])).

fof(f496,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f495,f72])).

fof(f495,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f494,f71])).

fof(f494,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f493,f68])).

fof(f493,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f246,f155])).

fof(f155,plain,(
    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f119,f71])).

fof(f119,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f72,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f246,plain,
    ( ! [X11] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X11)
        | v2_struct_0(X11)
        | ~ l1_pre_topc(X11)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_tex_2(sK1,X11) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl6_12
  <=> ! [X11] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_struct_0(X11)
        | ~ l1_pre_topc(X11)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X11)
        | v2_tex_2(sK1,X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f313,plain,
    ( spl6_15
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f308,f310,f277])).

fof(f277,plain,
    ( spl6_15
  <=> v4_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f308,plain,
    ( ~ v1_xboole_0(sK2(sK0,sK1))
    | v4_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f307,f69])).

fof(f307,plain,
    ( ~ v1_xboole_0(sK2(sK0,sK1))
    | v4_pre_topc(sK2(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f265,f71])).

fof(f265,plain,
    ( ~ v1_xboole_0(sK2(sK0,sK1))
    | v4_pre_topc(sK2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f143,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f143,plain,(
    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f142,f68])).

fof(f142,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f141,f69])).

fof(f141,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f140,f71])).

fof(f140,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f116,f73])).

fof(f116,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f72,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f280,plain,
    ( spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f271,f277,f273])).

fof(f271,plain,
    ( ~ v4_pre_topc(sK2(sK0,sK1),sK0)
    | sK2(sK0,sK1) = k2_pre_topc(sK0,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f260,f71])).

fof(f260,plain,
    ( ~ v4_pre_topc(sK2(sK0,sK1),sK0)
    | sK2(sK0,sK1) = k2_pre_topc(sK0,sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f143,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f258,plain,
    ( spl6_3
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f256,f184])).

fof(f184,plain,(
    l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f177,f71])).

fof(f177,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f155,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f256,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl6_3
    | ~ spl6_6 ),
    inference(resolution,[],[f255,f75])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
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

fof(f255,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f254,f153])).

fof(f153,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f151])).

fof(f254,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f253,f123])).

fof(f123,plain,(
    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f112,f71])).

fof(f112,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f72,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f253,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_pre_topc(sK0,sK1)))
    | ~ spl6_6 ),
    inference(resolution,[],[f212,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f212,plain,
    ( v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl6_6
  <=> v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f247,plain,
    ( spl6_6
    | spl6_12 ),
    inference(avatar_split_clause,[],[f243,f245,f210])).

fof(f243,plain,(
    ! [X11] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X11)))
      | v2_tex_2(sK1,X11)
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X11)
      | v2_struct_0(k1_pre_topc(sK0,sK1))
      | ~ l1_pre_topc(X11)
      | v2_struct_0(X11) ) ),
    inference(subsumption_resolution,[],[f200,f181])).

fof(f181,plain,(
    v1_tdlat_3(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f180,f68])).

fof(f180,plain,
    ( v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f179,f69])).

fof(f179,plain,
    ( v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f178,f70])).

fof(f70,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f178,plain,
    ( v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f175,f71])).

fof(f175,plain,
    ( v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f155,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_tdlat_3(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v1_tdlat_3(X1) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f200,plain,(
    ! [X11] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X11)))
      | ~ v1_tdlat_3(k1_pre_topc(sK0,sK1))
      | v2_tex_2(sK1,X11)
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X11)
      | v2_struct_0(k1_pre_topc(sK0,sK1))
      | ~ l1_pre_topc(X11)
      | v2_struct_0(X11) ) ),
    inference(superposition,[],[f105,f123])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f174,plain,
    ( ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f165,f171,f167])).

fof(f165,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ r1_tarski(sK1,sK2(sK0,sK1)) ),
    inference(resolution,[],[f147,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:25:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (30322)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (30330)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (30322)Refutation not found, incomplete strategy% (30322)------------------------------
% 0.22/0.52  % (30322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30322)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30322)Memory used [KB]: 1663
% 0.22/0.52  % (30322)Time elapsed: 0.002 s
% 0.22/0.52  % (30322)------------------------------
% 0.22/0.52  % (30322)------------------------------
% 0.22/0.52  % (30331)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (30327)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (30341)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (30338)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (30325)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (30344)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (30347)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (30333)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (30323)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (30331)Refutation not found, incomplete strategy% (30331)------------------------------
% 0.22/0.53  % (30331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30331)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30331)Memory used [KB]: 10618
% 0.22/0.53  % (30331)Time elapsed: 0.002 s
% 0.22/0.53  % (30331)------------------------------
% 0.22/0.53  % (30331)------------------------------
% 0.22/0.54  % (30349)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (30326)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (30330)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f588,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f174,f247,f258,f280,f313,f498,f506,f509,f586])).
% 0.22/0.54  fof(f586,plain,(
% 0.22/0.54    ~spl6_5 | ~spl6_14),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f585])).
% 0.22/0.54  fof(f585,plain,(
% 0.22/0.54    $false | (~spl6_5 | ~spl6_14)),
% 0.22/0.54    inference(subsumption_resolution,[],[f548,f158])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,X0) = X0) )),
% 0.22/0.54    inference(resolution,[],[f120,f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~sP5(X0) | k9_subset_1(X0,X1,X1) = X1) )),
% 0.22/0.54    inference(general_splitting,[],[f104,f109_D])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | sP5(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f109_D])).
% 0.22/0.54  fof(f109_D,plain,(
% 0.22/0.54    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(X0)) ) <=> ~sP5(X0)) )),
% 0.22/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    sP5(u1_struct_0(sK0))),
% 0.22/0.54    inference(resolution,[],[f72,f109])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f50,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.22/0.54    inference(negated_conjecture,[],[f19])).
% 0.22/0.54  fof(f19,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.22/0.54  fof(f548,plain,(
% 0.22/0.54    sK1 != k9_subset_1(u1_struct_0(sK0),sK1,sK1) | (~spl6_5 | ~spl6_14)),
% 0.22/0.54    inference(backward_demodulation,[],[f434,f173])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    sK1 = sK2(sK0,sK1) | ~spl6_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f171])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    spl6_5 <=> sK1 = sK2(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.54  fof(f434,plain,(
% 0.22/0.54    sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK0,sK1)) | ~spl6_14),
% 0.22/0.54    inference(subsumption_resolution,[],[f433,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ~v2_struct_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f51])).
% 0.22/0.54  fof(f433,plain,(
% 0.22/0.54    sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK0,sK1)) | v2_struct_0(sK0) | ~spl6_14),
% 0.22/0.54    inference(subsumption_resolution,[],[f432,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    v2_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f51])).
% 0.22/0.54  fof(f432,plain,(
% 0.22/0.54    sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_14),
% 0.22/0.54    inference(subsumption_resolution,[],[f431,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f51])).
% 0.22/0.54  fof(f431,plain,(
% 0.22/0.54    sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_14),
% 0.22/0.54    inference(subsumption_resolution,[],[f430,f72])).
% 0.22/0.54  fof(f430,plain,(
% 0.22/0.54    sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_14),
% 0.22/0.54    inference(subsumption_resolution,[],[f429,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ~v2_tex_2(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f51])).
% 0.22/0.54  fof(f429,plain,(
% 0.22/0.54    sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK0,sK1)) | v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_14),
% 0.22/0.54    inference(superposition,[],[f86,f275])).
% 0.22/0.54  fof(f275,plain,(
% 0.22/0.54    sK2(sK0,sK1) = k2_pre_topc(sK0,sK2(sK0,sK1)) | ~spl6_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f273])).
% 0.22/0.54  fof(f273,plain,(
% 0.22/0.54    spl6_14 <=> sK2(sK0,sK1) = k2_pre_topc(sK0,sK2(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) | v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(rectify,[],[f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 0.22/0.54  fof(f509,plain,(
% 0.22/0.54    ~spl6_3 | spl6_4),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f508])).
% 0.22/0.54  fof(f508,plain,(
% 0.22/0.54    $false | (~spl6_3 | spl6_4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f334,f152])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    v1_xboole_0(sK1) | ~spl6_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f151])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    spl6_3 <=> v1_xboole_0(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.54  fof(f334,plain,(
% 0.22/0.54    ~v1_xboole_0(sK1) | spl6_4),
% 0.22/0.54    inference(resolution,[],[f189,f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(rectify,[],[f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    r2_hidden(sK4(sK1,sK2(sK0,sK1)),sK1) | spl6_4),
% 0.22/0.54    inference(resolution,[],[f169,f102])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f65,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    ~r1_tarski(sK1,sK2(sK0,sK1)) | spl6_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f167])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    spl6_4 <=> r1_tarski(sK1,sK2(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.54  fof(f506,plain,(
% 0.22/0.54    ~spl6_3 | spl6_19),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f505])).
% 0.22/0.54  fof(f505,plain,(
% 0.22/0.54    $false | (~spl6_3 | spl6_19)),
% 0.22/0.54    inference(subsumption_resolution,[],[f152,f485])).
% 0.22/0.54  fof(f485,plain,(
% 0.22/0.54    ~v1_xboole_0(sK1) | spl6_19),
% 0.22/0.54    inference(resolution,[],[f480,f91])).
% 0.22/0.54  fof(f480,plain,(
% 0.22/0.54    r2_hidden(sK3(sK2(sK0,sK1)),sK1) | spl6_19),
% 0.22/0.54    inference(resolution,[],[f469,f164])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK2(sK0,sK1)) | r2_hidden(X0,sK1)) )),
% 0.22/0.54    inference(resolution,[],[f147,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f67])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    r1_tarski(sK2(sK0,sK1),sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f146,f68])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    r1_tarski(sK2(sK0,sK1),sK1) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f145,f69])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    r1_tarski(sK2(sK0,sK1),sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f144,f71])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    r1_tarski(sK2(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f117,f73])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    r1_tarski(sK2(sK0,sK1),sK1) | v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f72,f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f55])).
% 0.22/0.54  fof(f469,plain,(
% 0.22/0.54    r2_hidden(sK3(sK2(sK0,sK1)),sK2(sK0,sK1)) | spl6_19),
% 0.22/0.54    inference(resolution,[],[f312,f92])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f60])).
% 0.22/0.54  fof(f312,plain,(
% 0.22/0.54    ~v1_xboole_0(sK2(sK0,sK1)) | spl6_19),
% 0.22/0.54    inference(avatar_component_clause,[],[f310])).
% 0.22/0.54  fof(f310,plain,(
% 0.22/0.54    spl6_19 <=> v1_xboole_0(sK2(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.54  fof(f498,plain,(
% 0.22/0.54    ~spl6_12),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f497])).
% 0.22/0.54  fof(f497,plain,(
% 0.22/0.54    $false | ~spl6_12),
% 0.22/0.54    inference(subsumption_resolution,[],[f496,f73])).
% 0.22/0.54  fof(f496,plain,(
% 0.22/0.54    v2_tex_2(sK1,sK0) | ~spl6_12),
% 0.22/0.54    inference(subsumption_resolution,[],[f495,f72])).
% 0.22/0.54  fof(f495,plain,(
% 0.22/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0) | ~spl6_12),
% 0.22/0.54    inference(subsumption_resolution,[],[f494,f71])).
% 0.22/0.54  fof(f494,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0) | ~spl6_12),
% 0.22/0.54    inference(subsumption_resolution,[],[f493,f68])).
% 0.22/0.54  fof(f493,plain,(
% 0.22/0.54    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0) | ~spl6_12),
% 0.22/0.54    inference(resolution,[],[f246,f155])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f119,f71])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f72,f97])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.22/0.54  fof(f246,plain,(
% 0.22/0.54    ( ! [X11] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X11) | v2_struct_0(X11) | ~l1_pre_topc(X11) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X11))) | v2_tex_2(sK1,X11)) ) | ~spl6_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f245])).
% 0.22/0.54  fof(f245,plain,(
% 0.22/0.54    spl6_12 <=> ! [X11] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X11))) | v2_struct_0(X11) | ~l1_pre_topc(X11) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X11) | v2_tex_2(sK1,X11))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.54  fof(f313,plain,(
% 0.22/0.54    spl6_15 | ~spl6_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f308,f310,f277])).
% 0.22/0.54  fof(f277,plain,(
% 0.22/0.54    spl6_15 <=> v4_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.54  fof(f308,plain,(
% 0.22/0.54    ~v1_xboole_0(sK2(sK0,sK1)) | v4_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f307,f69])).
% 0.22/0.54  fof(f307,plain,(
% 0.22/0.54    ~v1_xboole_0(sK2(sK0,sK1)) | v4_pre_topc(sK2(sK0,sK1),sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f265,f71])).
% 0.22/0.54  fof(f265,plain,(
% 0.22/0.54    ~v1_xboole_0(sK2(sK0,sK1)) | v4_pre_topc(sK2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f143,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f142,f68])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f141,f69])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f140,f71])).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f116,f73])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f72,f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f55])).
% 0.22/0.54  fof(f280,plain,(
% 0.22/0.54    spl6_14 | ~spl6_15),
% 0.22/0.54    inference(avatar_split_clause,[],[f271,f277,f273])).
% 0.22/0.54  fof(f271,plain,(
% 0.22/0.54    ~v4_pre_topc(sK2(sK0,sK1),sK0) | sK2(sK0,sK1) = k2_pre_topc(sK0,sK2(sK0,sK1))),
% 0.22/0.54    inference(subsumption_resolution,[],[f260,f71])).
% 0.22/0.54  fof(f260,plain,(
% 0.22/0.54    ~v4_pre_topc(sK2(sK0,sK1),sK0) | sK2(sK0,sK1) = k2_pre_topc(sK0,sK2(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f143,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.54  fof(f258,plain,(
% 0.22/0.54    spl6_3 | ~spl6_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f257])).
% 0.22/0.54  fof(f257,plain,(
% 0.22/0.54    $false | (spl6_3 | ~spl6_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f256,f184])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.22/0.54    inference(subsumption_resolution,[],[f177,f71])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f155,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.54  fof(f256,plain,(
% 0.22/0.54    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | (spl6_3 | ~spl6_6)),
% 0.22/0.54    inference(resolution,[],[f255,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.54  fof(f255,plain,(
% 0.22/0.54    ~l1_struct_0(k1_pre_topc(sK0,sK1)) | (spl6_3 | ~spl6_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f254,f153])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    ~v1_xboole_0(sK1) | spl6_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f151])).
% 0.22/0.54  fof(f254,plain,(
% 0.22/0.54    v1_xboole_0(sK1) | ~l1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl6_6),
% 0.22/0.54    inference(forward_demodulation,[],[f253,f123])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.22/0.54    inference(subsumption_resolution,[],[f112,f71])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f72,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.22/0.54  fof(f253,plain,(
% 0.22/0.54    ~l1_struct_0(k1_pre_topc(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_pre_topc(sK0,sK1))) | ~spl6_6),
% 0.22/0.54    inference(resolution,[],[f212,f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).
% 0.22/0.54  fof(f212,plain,(
% 0.22/0.54    v2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl6_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f210])).
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    spl6_6 <=> v2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.54  fof(f247,plain,(
% 0.22/0.54    spl6_6 | spl6_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f243,f245,f210])).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    ( ! [X11] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X11))) | v2_tex_2(sK1,X11) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X11) | v2_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(X11) | v2_struct_0(X11)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f200,f181])).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    v1_tdlat_3(k1_pre_topc(sK0,sK1))),
% 0.22/0.54    inference(subsumption_resolution,[],[f180,f68])).
% 0.22/0.54  fof(f180,plain,(
% 0.22/0.54    v1_tdlat_3(k1_pre_topc(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f179,f69])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    v1_tdlat_3(k1_pre_topc(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f178,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    v1_tdlat_3(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f51])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    v1_tdlat_3(k1_pre_topc(sK0,sK1)) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f175,f71])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    v1_tdlat_3(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f155,f82])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_tdlat_3(X1) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v1_tdlat_3(X1)))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    ( ! [X11] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X11))) | ~v1_tdlat_3(k1_pre_topc(sK0,sK1)) | v2_tex_2(sK1,X11) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X11) | v2_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(X11) | v2_struct_0(X11)) )),
% 0.22/0.54    inference(superposition,[],[f105,f123])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f88])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    ~spl6_4 | spl6_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f165,f171,f167])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    sK1 = sK2(sK0,sK1) | ~r1_tarski(sK1,sK2(sK0,sK1))),
% 0.22/0.54    inference(resolution,[],[f147,f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (30330)------------------------------
% 0.22/0.54  % (30330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30330)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (30330)Memory used [KB]: 11001
% 0.22/0.54  % (30330)Time elapsed: 0.126 s
% 0.22/0.54  % (30330)------------------------------
% 0.22/0.54  % (30330)------------------------------
% 0.22/0.54  % (30348)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (30337)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (30321)Success in time 0.175 s
%------------------------------------------------------------------------------
