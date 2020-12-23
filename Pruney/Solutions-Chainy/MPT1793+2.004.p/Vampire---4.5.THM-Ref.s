%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 431 expanded)
%              Number of leaves         :   42 ( 210 expanded)
%              Depth                    :    9
%              Number of atoms          :  681 (2784 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f885,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f226,f231,f271,f272,f304,f335,f336,f339,f343,f348,f358,f363,f368,f369,f374,f408,f412,f429,f452,f591,f688,f718,f867,f884])).

fof(f884,plain,
    ( ~ spl6_35
    | ~ spl6_94 ),
    inference(avatar_split_clause,[],[f881,f749,f301])).

fof(f301,plain,
    ( spl6_35
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f749,plain,
    ( spl6_94
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f881,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl6_94 ),
    inference(resolution,[],[f751,f278])).

fof(f278,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f56,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

% (2980)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f56,plain,(
    r1_xboole_0(u1_struct_0(sK2),sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & r1_xboole_0(u1_struct_0(sK2),sK1)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f44,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                    & m1_subset_1(X3,u1_struct_0(X2)) )
                & r1_xboole_0(u1_struct_0(X2),X1)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_xboole_0(u1_struct_0(X2),X1)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_xboole_0(u1_struct_0(X2),sK1)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3)
            & m1_subset_1(X3,u1_struct_0(X2)) )
        & r1_xboole_0(u1_struct_0(X2),sK1)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3)
          & m1_subset_1(X3,u1_struct_0(sK2)) )
      & r1_xboole_0(u1_struct_0(sK2),sK1)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X3] :
        ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3)
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_xboole_0(u1_struct_0(X2),X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).

fof(f751,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f749])).

fof(f867,plain,
    ( spl6_94
    | ~ spl6_50
    | ~ spl6_40
    | spl6_52 ),
    inference(avatar_split_clause,[],[f864,f426,f341,f418,f749])).

fof(f418,plain,
    ( spl6_50
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f341,plain,
    ( spl6_40
  <=> ! [X0] :
        ( r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f426,plain,
    ( spl6_52
  <=> r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f864,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK3,sK1)
    | ~ spl6_40
    | spl6_52 ),
    inference(resolution,[],[f342,f428])).

fof(f428,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | spl6_52 ),
    inference(avatar_component_clause,[],[f426])).

fof(f342,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f341])).

fof(f718,plain,
    ( spl6_50
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f713,f410,f418])).

fof(f410,plain,
    ( spl6_48
  <=> ! [X3] :
        ( m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f713,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl6_48 ),
    inference(resolution,[],[f411,f57])).

fof(f57,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f411,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK2))
        | m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f410])).

fof(f688,plain,
    ( ~ spl6_34
    | spl6_21
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f651,f223,f228,f297])).

fof(f297,plain,
    ( spl6_34
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f228,plain,
    ( spl6_21
  <=> v1_xboole_0(sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f223,plain,
    ( spl6_20
  <=> m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f651,plain,
    ( v1_xboole_0(sK4(sK2))
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl6_20 ),
    inference(resolution,[],[f225,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f225,plain,
    ( m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f223])).

fof(f591,plain,(
    spl6_51 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | spl6_51 ),
    inference(resolution,[],[f424,f57])).

% (2974)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (2964)Refutation not found, incomplete strategy% (2964)------------------------------
% (2964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2964)Termination reason: Refutation not found, incomplete strategy

% (2964)Memory used [KB]: 6268
% (2964)Time elapsed: 0.092 s
% (2964)------------------------------
% (2964)------------------------------
% (2965)Termination reason: Refutation not found, incomplete strategy

% (2965)Memory used [KB]: 10618
% (2965)Time elapsed: 0.078 s
% (2965)------------------------------
% (2965)------------------------------
% (2966)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (2974)Refutation not found, incomplete strategy% (2974)------------------------------
% (2974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2974)Termination reason: Refutation not found, incomplete strategy

% (2974)Memory used [KB]: 6268
% (2974)Time elapsed: 0.079 s
% (2974)------------------------------
% (2974)------------------------------
% (2970)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (2979)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (2971)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f424,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl6_51 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl6_51
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f452,plain,(
    spl6_49 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | spl6_49 ),
    inference(resolution,[],[f416,f55])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f416,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl6_49 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl6_49
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f429,plain,
    ( spl6_41
    | ~ spl6_42
    | ~ spl6_46
    | spl6_15
    | ~ spl6_3
    | ~ spl6_1
    | ~ spl6_43
    | ~ spl6_44
    | ~ spl6_45
    | spl6_31
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_51
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f337,f426,f422,f418,f414,f285,f365,f360,f355,f100,f108,f187,f371,f350,f345])).

fof(f345,plain,
    ( spl6_41
  <=> v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f350,plain,
    ( spl6_42
  <=> v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f371,plain,
    ( spl6_46
  <=> l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f187,plain,
    ( spl6_15
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f108,plain,
    ( spl6_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f100,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f355,plain,
    ( spl6_43
  <=> v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f360,plain,
    ( spl6_44
  <=> v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f365,plain,
    ( spl6_45
  <=> m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f285,plain,
    ( spl6_31
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f337,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f58,f83])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f58,plain,(
    ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f412,plain,
    ( spl6_15
    | ~ spl6_1
    | spl6_31
    | spl6_48 ),
    inference(avatar_split_clause,[],[f267,f410,f285,f100,f187])).

fof(f267,plain,(
    ! [X3] :
      ( m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f55,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f408,plain,(
    ~ spl6_31 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | ~ spl6_31 ),
    inference(resolution,[],[f287,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f287,plain,
    ( v2_struct_0(sK2)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f285])).

fof(f374,plain,
    ( spl6_15
    | ~ spl6_3
    | ~ spl6_1
    | spl6_46 ),
    inference(avatar_split_clause,[],[f312,f371,f100,f108,f187])).

fof(f312,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f369,plain,
    ( spl6_15
    | ~ spl6_3
    | ~ spl6_1
    | spl6_42 ),
    inference(avatar_split_clause,[],[f311,f350,f100,f108,f187])).

fof(f311,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f368,plain,
    ( spl6_15
    | ~ spl6_3
    | ~ spl6_1
    | spl6_45 ),
    inference(avatar_split_clause,[],[f310,f365,f100,f108,f187])).

fof(f310,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f363,plain,
    ( spl6_15
    | ~ spl6_3
    | ~ spl6_1
    | spl6_44 ),
    inference(avatar_split_clause,[],[f309,f360,f100,f108,f187])).

fof(f309,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f358,plain,
    ( spl6_15
    | ~ spl6_3
    | ~ spl6_1
    | spl6_43 ),
    inference(avatar_split_clause,[],[f308,f355,f100,f108,f187])).

fof(f308,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f348,plain,
    ( spl6_15
    | ~ spl6_3
    | ~ spl6_1
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f306,f345,f100,f108,f187])).

fof(f306,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(f343,plain,
    ( spl6_15
    | ~ spl6_3
    | ~ spl6_1
    | spl6_40 ),
    inference(avatar_split_clause,[],[f305,f341,f100,f108,f187])).

fof(f305,plain,(
    ! [X0] :
      ( r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0)
      | r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f53,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

% (2969)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ r2_hidden(X2,X1)
               => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).

fof(f339,plain,(
    ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | ~ spl6_15 ),
    inference(resolution,[],[f189,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f189,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f187])).

fof(f336,plain,
    ( ~ spl6_3
    | ~ spl6_1
    | spl6_18 ),
    inference(avatar_split_clause,[],[f265,f215,f100,f108])).

fof(f215,plain,
    ( spl6_18
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f265,plain,
    ( v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f55,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f335,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | spl6_3 ),
    inference(resolution,[],[f110,f51])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f110,plain,
    ( ~ v2_pre_topc(sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f304,plain,
    ( spl6_34
    | spl6_35 ),
    inference(avatar_split_clause,[],[f283,f301,f297])).

fof(f283,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f57,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f272,plain,
    ( ~ spl6_1
    | spl6_16 ),
    inference(avatar_split_clause,[],[f268,f207,f100])).

fof(f207,plain,
    ( spl6_16
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f268,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f271,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f102,f52])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f231,plain,
    ( ~ spl6_18
    | ~ spl6_16
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f195,f228,f207,f215])).

fof(f195,plain,
    ( ~ v1_xboole_0(sK4(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f54,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK4(X0),X0)
        & v3_pre_topc(sK4(X0),X0)
        & ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK4(X0),X0)
        & v3_pre_topc(sK4(X0),X0)
        & ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f226,plain,
    ( ~ spl6_18
    | ~ spl6_16
    | spl6_20 ),
    inference(avatar_split_clause,[],[f194,f223,f207,f215])).

fof(f194,plain,
    ( m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f54,f64])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:29:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.46  % (2976)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.47  % (2983)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.19/0.48  % (2968)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.48  % (2967)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.49  % (2965)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (2965)Refutation not found, incomplete strategy% (2965)------------------------------
% 0.19/0.49  % (2965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (2976)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.50  % (2964)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f885,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f226,f231,f271,f272,f304,f335,f336,f339,f343,f348,f358,f363,f368,f369,f374,f408,f412,f429,f452,f591,f688,f718,f867,f884])).
% 0.19/0.50  fof(f884,plain,(
% 0.19/0.50    ~spl6_35 | ~spl6_94),
% 0.19/0.50    inference(avatar_split_clause,[],[f881,f749,f301])).
% 0.19/0.50  fof(f301,plain,(
% 0.19/0.50    spl6_35 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.19/0.50  fof(f749,plain,(
% 0.19/0.50    spl6_94 <=> r2_hidden(sK3,sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).
% 0.19/0.50  fof(f881,plain,(
% 0.19/0.50    ~r2_hidden(sK3,u1_struct_0(sK2)) | ~spl6_94),
% 0.19/0.50    inference(resolution,[],[f751,f278])).
% 0.19/0.50  fof(f278,plain,(
% 0.19/0.50    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,u1_struct_0(sK2))) )),
% 0.19/0.50    inference(resolution,[],[f56,f71])).
% 0.19/0.50  fof(f71,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f49])).
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f48])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f16])).
% 0.19/0.50  % (2980)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.50    inference(rectify,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    r1_xboole_0(u1_struct_0(sK2),sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f45])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    (((~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2))) & r1_xboole_0(u1_struct_0(sK2),sK1) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f44,f43,f42,f41])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    ? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),sK1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),sK1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3) & m1_subset_1(X3,u1_struct_0(sK2))) & r1_xboole_0(u1_struct_0(sK2),sK1) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    ? [X3] : (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3) & m1_subset_1(X3,u1_struct_0(sK2))) => (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f15])).
% 0.19/0.50  fof(f15,negated_conjecture,(
% 0.19/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 0.19/0.50    inference(negated_conjecture,[],[f14])).
% 0.19/0.50  fof(f14,conjecture,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).
% 0.19/0.50  fof(f751,plain,(
% 0.19/0.50    r2_hidden(sK3,sK1) | ~spl6_94),
% 0.19/0.50    inference(avatar_component_clause,[],[f749])).
% 0.19/0.50  fof(f867,plain,(
% 0.19/0.50    spl6_94 | ~spl6_50 | ~spl6_40 | spl6_52),
% 0.19/0.50    inference(avatar_split_clause,[],[f864,f426,f341,f418,f749])).
% 0.19/0.50  fof(f418,plain,(
% 0.19/0.50    spl6_50 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 0.19/0.50  fof(f341,plain,(
% 0.19/0.50    spl6_40 <=> ! [X0] : (r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.19/0.50  fof(f426,plain,(
% 0.19/0.50    spl6_52 <=> r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 0.19/0.50  fof(f864,plain,(
% 0.19/0.50    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK3,sK1) | (~spl6_40 | spl6_52)),
% 0.19/0.50    inference(resolution,[],[f342,f428])).
% 0.19/0.50  fof(f428,plain,(
% 0.19/0.50    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | spl6_52),
% 0.19/0.50    inference(avatar_component_clause,[],[f426])).
% 0.19/0.50  fof(f342,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | ~spl6_40),
% 0.19/0.50    inference(avatar_component_clause,[],[f341])).
% 0.19/0.50  fof(f718,plain,(
% 0.19/0.50    spl6_50 | ~spl6_48),
% 0.19/0.50    inference(avatar_split_clause,[],[f713,f410,f418])).
% 0.19/0.50  fof(f410,plain,(
% 0.19/0.50    spl6_48 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK2)))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 0.19/0.50  fof(f713,plain,(
% 0.19/0.50    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl6_48),
% 0.19/0.50    inference(resolution,[],[f411,f57])).
% 0.19/0.50  fof(f57,plain,(
% 0.19/0.50    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.19/0.50    inference(cnf_transformation,[],[f45])).
% 0.19/0.50  fof(f411,plain,(
% 0.19/0.50    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK2)) | m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl6_48),
% 0.19/0.50    inference(avatar_component_clause,[],[f410])).
% 0.19/0.50  fof(f688,plain,(
% 0.19/0.50    ~spl6_34 | spl6_21 | ~spl6_20),
% 0.19/0.50    inference(avatar_split_clause,[],[f651,f223,f228,f297])).
% 0.19/0.50  fof(f297,plain,(
% 0.19/0.50    spl6_34 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.19/0.50  fof(f228,plain,(
% 0.19/0.50    spl6_21 <=> v1_xboole_0(sK4(sK2))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.19/0.50  fof(f223,plain,(
% 0.19/0.50    spl6_20 <=> m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.19/0.50  fof(f651,plain,(
% 0.19/0.50    v1_xboole_0(sK4(sK2)) | ~v1_xboole_0(u1_struct_0(sK2)) | ~spl6_20),
% 0.19/0.50    inference(resolution,[],[f225,f59])).
% 0.19/0.50  fof(f59,plain,(
% 0.19/0.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.19/0.50  fof(f225,plain,(
% 0.19/0.50    m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl6_20),
% 0.19/0.50    inference(avatar_component_clause,[],[f223])).
% 0.19/0.50  fof(f591,plain,(
% 0.19/0.50    spl6_51),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f589])).
% 0.19/0.50  fof(f589,plain,(
% 0.19/0.50    $false | spl6_51),
% 0.19/0.50    inference(resolution,[],[f424,f57])).
% 0.19/0.50  % (2974)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.50  % (2964)Refutation not found, incomplete strategy% (2964)------------------------------
% 0.19/0.50  % (2964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (2964)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (2964)Memory used [KB]: 6268
% 0.19/0.50  % (2964)Time elapsed: 0.092 s
% 0.19/0.50  % (2964)------------------------------
% 0.19/0.50  % (2964)------------------------------
% 0.19/0.50  % (2965)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (2965)Memory used [KB]: 10618
% 0.19/0.50  % (2965)Time elapsed: 0.078 s
% 0.19/0.50  % (2965)------------------------------
% 0.19/0.50  % (2965)------------------------------
% 0.19/0.50  % (2966)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.50  % (2974)Refutation not found, incomplete strategy% (2974)------------------------------
% 0.19/0.50  % (2974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (2974)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (2974)Memory used [KB]: 6268
% 0.19/0.50  % (2974)Time elapsed: 0.079 s
% 0.19/0.50  % (2974)------------------------------
% 0.19/0.50  % (2974)------------------------------
% 0.19/0.50  % (2970)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.50  % (2979)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.50  % (2971)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.51  fof(f424,plain,(
% 0.19/0.51    ~m1_subset_1(sK3,u1_struct_0(sK2)) | spl6_51),
% 0.19/0.51    inference(avatar_component_clause,[],[f422])).
% 0.19/0.51  fof(f422,plain,(
% 0.19/0.51    spl6_51 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 0.19/0.51  fof(f452,plain,(
% 0.19/0.51    spl6_49),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f451])).
% 0.19/0.51  fof(f451,plain,(
% 0.19/0.51    $false | spl6_49),
% 0.19/0.51    inference(resolution,[],[f416,f55])).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    m1_pre_topc(sK2,sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f45])).
% 0.19/0.51  fof(f416,plain,(
% 0.19/0.51    ~m1_pre_topc(sK2,sK0) | spl6_49),
% 0.19/0.51    inference(avatar_component_clause,[],[f414])).
% 0.19/0.51  fof(f414,plain,(
% 0.19/0.51    spl6_49 <=> m1_pre_topc(sK2,sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 0.19/0.51  fof(f429,plain,(
% 0.19/0.51    spl6_41 | ~spl6_42 | ~spl6_46 | spl6_15 | ~spl6_3 | ~spl6_1 | ~spl6_43 | ~spl6_44 | ~spl6_45 | spl6_31 | ~spl6_49 | ~spl6_50 | ~spl6_51 | ~spl6_52),
% 0.19/0.51    inference(avatar_split_clause,[],[f337,f426,f422,f418,f414,f285,f365,f360,f355,f100,f108,f187,f371,f350,f345])).
% 0.19/0.51  fof(f345,plain,(
% 0.19/0.51    spl6_41 <=> v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.19/0.51  fof(f350,plain,(
% 0.19/0.51    spl6_42 <=> v2_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.19/0.51  fof(f371,plain,(
% 0.19/0.51    spl6_46 <=> l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.19/0.51  fof(f187,plain,(
% 0.19/0.51    spl6_15 <=> v2_struct_0(sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.19/0.51  fof(f108,plain,(
% 0.19/0.51    spl6_3 <=> v2_pre_topc(sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.19/0.51  fof(f100,plain,(
% 0.19/0.51    spl6_1 <=> l1_pre_topc(sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.19/0.51  fof(f355,plain,(
% 0.19/0.51    spl6_43 <=> v1_funct_1(k7_tmap_1(sK0,sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.19/0.51  fof(f360,plain,(
% 0.19/0.51    spl6_44 <=> v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.19/0.51  fof(f365,plain,(
% 0.19/0.51    spl6_45 <=> m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.19/0.51  fof(f285,plain,(
% 0.19/0.51    spl6_31 <=> v2_struct_0(sK2)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.19/0.51  fof(f337,plain,(
% 0.19/0.51    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.19/0.51    inference(resolution,[],[f58,f83])).
% 0.19/0.51  fof(f83,plain,(
% 0.19/0.51    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(equality_resolution,[],[f63])).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f26])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.19/0.51  fof(f58,plain,(
% 0.19/0.51    ~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)),
% 0.19/0.51    inference(cnf_transformation,[],[f45])).
% 0.19/0.51  fof(f412,plain,(
% 0.19/0.51    spl6_15 | ~spl6_1 | spl6_31 | spl6_48),
% 0.19/0.51    inference(avatar_split_clause,[],[f267,f410,f285,f100,f187])).
% 0.19/0.51  fof(f267,plain,(
% 0.19/0.51    ( ! [X3] : (m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK2)) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.51    inference(resolution,[],[f55,f61])).
% 0.19/0.51  fof(f61,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.19/0.51  fof(f408,plain,(
% 0.19/0.51    ~spl6_31),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f407])).
% 0.19/0.51  fof(f407,plain,(
% 0.19/0.51    $false | ~spl6_31),
% 0.19/0.51    inference(resolution,[],[f287,f54])).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    ~v2_struct_0(sK2)),
% 0.19/0.51    inference(cnf_transformation,[],[f45])).
% 0.19/0.51  fof(f287,plain,(
% 0.19/0.51    v2_struct_0(sK2) | ~spl6_31),
% 0.19/0.51    inference(avatar_component_clause,[],[f285])).
% 0.19/0.51  fof(f374,plain,(
% 0.19/0.51    spl6_15 | ~spl6_3 | ~spl6_1 | spl6_46),
% 0.19/0.51    inference(avatar_split_clause,[],[f312,f371,f100,f108,f187])).
% 0.19/0.51  fof(f312,plain,(
% 0.19/0.51    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.51    inference(resolution,[],[f53,f82])).
% 0.19/0.51  fof(f82,plain,(
% 0.19/0.51    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f39])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.51    inference(cnf_transformation,[],[f45])).
% 0.19/0.51  fof(f369,plain,(
% 0.19/0.51    spl6_15 | ~spl6_3 | ~spl6_1 | spl6_42),
% 0.19/0.51    inference(avatar_split_clause,[],[f311,f350,f100,f108,f187])).
% 0.19/0.51  fof(f311,plain,(
% 0.19/0.51    v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.51    inference(resolution,[],[f53,f81])).
% 0.19/0.51  fof(f81,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f40])).
% 0.19/0.51  fof(f368,plain,(
% 0.19/0.51    spl6_15 | ~spl6_3 | ~spl6_1 | spl6_45),
% 0.19/0.51    inference(avatar_split_clause,[],[f310,f365,f100,f108,f187])).
% 0.19/0.51  fof(f310,plain,(
% 0.19/0.51    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.51    inference(resolution,[],[f53,f79])).
% 0.19/0.51  fof(f79,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f38])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 0.19/0.51  fof(f363,plain,(
% 0.19/0.51    spl6_15 | ~spl6_3 | ~spl6_1 | spl6_44),
% 0.19/0.51    inference(avatar_split_clause,[],[f309,f360,f100,f108,f187])).
% 0.19/0.51  fof(f309,plain,(
% 0.19/0.51    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.51    inference(resolution,[],[f53,f78])).
% 0.19/0.51  fof(f78,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f38])).
% 0.19/0.51  fof(f358,plain,(
% 0.19/0.51    spl6_15 | ~spl6_3 | ~spl6_1 | spl6_43),
% 0.19/0.51    inference(avatar_split_clause,[],[f308,f355,f100,f108,f187])).
% 0.19/0.51  fof(f308,plain,(
% 0.19/0.51    v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.51    inference(resolution,[],[f53,f77])).
% 0.19/0.51  fof(f77,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f38])).
% 0.19/0.51  fof(f348,plain,(
% 0.19/0.51    spl6_15 | ~spl6_3 | ~spl6_1 | ~spl6_41),
% 0.19/0.51    inference(avatar_split_clause,[],[f306,f345,f100,f108,f187])).
% 0.19/0.51  fof(f306,plain,(
% 0.19/0.51    ~v2_struct_0(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.51    inference(resolution,[],[f53,f74])).
% 0.19/0.51  fof(f74,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v2_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f35])).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,axiom,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).
% 0.19/0.51  fof(f343,plain,(
% 0.19/0.51    spl6_15 | ~spl6_3 | ~spl6_1 | spl6_40),
% 0.19/0.51    inference(avatar_split_clause,[],[f305,f341,f100,f108,f187])).
% 0.19/0.51  fof(f305,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X0) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.51    inference(resolution,[],[f53,f62])).
% 0.19/0.51  fof(f62,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f12])).
% 0.19/0.51  % (2969)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.51  fof(f12,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~r2_hidden(X2,X1) => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).
% 0.19/0.51  fof(f339,plain,(
% 0.19/0.51    ~spl6_15),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f338])).
% 0.19/0.51  fof(f338,plain,(
% 0.19/0.51    $false | ~spl6_15),
% 0.19/0.51    inference(resolution,[],[f189,f50])).
% 0.19/0.51  fof(f50,plain,(
% 0.19/0.51    ~v2_struct_0(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f45])).
% 0.19/0.51  fof(f189,plain,(
% 0.19/0.51    v2_struct_0(sK0) | ~spl6_15),
% 0.19/0.51    inference(avatar_component_clause,[],[f187])).
% 0.19/0.51  fof(f336,plain,(
% 0.19/0.51    ~spl6_3 | ~spl6_1 | spl6_18),
% 0.19/0.51    inference(avatar_split_clause,[],[f265,f215,f100,f108])).
% 0.19/0.51  fof(f215,plain,(
% 0.19/0.51    spl6_18 <=> v2_pre_topc(sK2)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.19/0.51  fof(f265,plain,(
% 0.19/0.51    v2_pre_topc(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.19/0.51    inference(resolution,[],[f55,f68])).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.51    inference(flattening,[],[f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.19/0.51  fof(f335,plain,(
% 0.19/0.51    spl6_3),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f333])).
% 0.19/0.51  fof(f333,plain,(
% 0.19/0.51    $false | spl6_3),
% 0.19/0.51    inference(resolution,[],[f110,f51])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    v2_pre_topc(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f45])).
% 0.19/0.51  fof(f110,plain,(
% 0.19/0.51    ~v2_pre_topc(sK0) | spl6_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f108])).
% 0.19/0.51  fof(f304,plain,(
% 0.19/0.51    spl6_34 | spl6_35),
% 0.19/0.51    inference(avatar_split_clause,[],[f283,f301,f297])).
% 0.19/0.51  fof(f283,plain,(
% 0.19/0.51    r2_hidden(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.19/0.51    inference(resolution,[],[f57,f73])).
% 0.19/0.51  fof(f73,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f34])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.19/0.51    inference(flattening,[],[f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.19/0.51  fof(f272,plain,(
% 0.19/0.51    ~spl6_1 | spl6_16),
% 0.19/0.51    inference(avatar_split_clause,[],[f268,f207,f100])).
% 0.19/0.51  fof(f207,plain,(
% 0.19/0.51    spl6_16 <=> l1_pre_topc(sK2)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.19/0.51  fof(f268,plain,(
% 0.19/0.51    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.19/0.51    inference(resolution,[],[f55,f60])).
% 0.19/0.51  fof(f60,plain,(
% 0.19/0.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.19/0.51  fof(f271,plain,(
% 0.19/0.51    spl6_1),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f269])).
% 0.19/0.51  fof(f269,plain,(
% 0.19/0.51    $false | spl6_1),
% 0.19/0.51    inference(resolution,[],[f102,f52])).
% 0.19/0.51  fof(f52,plain,(
% 0.19/0.51    l1_pre_topc(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f45])).
% 0.19/0.51  fof(f102,plain,(
% 0.19/0.51    ~l1_pre_topc(sK0) | spl6_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f100])).
% 0.19/0.51  fof(f231,plain,(
% 0.19/0.51    ~spl6_18 | ~spl6_16 | ~spl6_21),
% 0.19/0.51    inference(avatar_split_clause,[],[f195,f228,f207,f215])).
% 0.19/0.51  fof(f195,plain,(
% 0.19/0.51    ~v1_xboole_0(sK4(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.19/0.51    inference(resolution,[],[f54,f65])).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_xboole_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f47])).
% 0.19/0.51  fof(f47,plain,(
% 0.19/0.51    ! [X0] : ((v4_pre_topc(sK4(X0),X0) & v3_pre_topc(sK4(X0),X0) & ~v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f46])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK4(X0),X0) & v3_pre_topc(sK4(X0),X0) & ~v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).
% 0.19/0.51  fof(f226,plain,(
% 0.19/0.51    ~spl6_18 | ~spl6_16 | spl6_20),
% 0.19/0.51    inference(avatar_split_clause,[],[f194,f223,f207,f215])).
% 0.19/0.51  fof(f194,plain,(
% 0.19/0.51    m1_subset_1(sK4(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.19/0.51    inference(resolution,[],[f54,f64])).
% 0.19/0.51  fof(f64,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f47])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (2976)------------------------------
% 0.19/0.51  % (2976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (2976)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (2976)Memory used [KB]: 6652
% 0.19/0.51  % (2976)Time elapsed: 0.075 s
% 0.19/0.51  % (2976)------------------------------
% 0.19/0.51  % (2976)------------------------------
% 0.19/0.51  % (2977)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.51  % (2978)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.51  % (2963)Success in time 0.158 s
%------------------------------------------------------------------------------
