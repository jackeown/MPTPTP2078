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
% DateTime   : Thu Dec  3 13:21:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 185 expanded)
%              Number of leaves         :   29 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  322 ( 669 expanded)
%              Number of equality atoms :   53 (  74 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f430,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f104,f406,f408,f410,f420,f423,f429])).

fof(f429,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | spl6_7 ),
    inference(resolution,[],[f419,f77])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f54,f51])).

fof(f51,plain,(
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

fof(f419,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl6_7
  <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f423,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | spl6_6 ),
    inference(resolution,[],[f421,f47])).

fof(f47,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v1_xboole_0(X1) )
   => ( ~ v2_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f421,plain,
    ( ~ l1_pre_topc(sK2)
    | spl6_6 ),
    inference(resolution,[],[f415,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f415,plain,
    ( ~ l1_struct_0(sK2)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl6_6
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f420,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_5 ),
    inference(avatar_split_clause,[],[f411,f403,f417,f413])).

fof(f403,plain,
    ( spl6_5
  <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f411,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ l1_struct_0(sK2)
    | spl6_5 ),
    inference(superposition,[],[f405,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f405,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f403])).

fof(f410,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | spl6_4 ),
    inference(resolution,[],[f401,f47])).

fof(f401,plain,
    ( ~ l1_pre_topc(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl6_4
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f408,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | spl6_3 ),
    inference(resolution,[],[f397,f46])).

fof(f46,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f397,plain,
    ( ~ v2_pre_topc(sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl6_3
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f406,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_2 ),
    inference(avatar_split_clause,[],[f392,f96,f403,f399,f395])).

fof(f96,plain,
    ( spl6_2
  <=> sP0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f392,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl6_2 ),
    inference(resolution,[],[f391,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f391,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | spl6_2 ),
    inference(trivial_inequality_removal,[],[f390])).

fof(f390,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ v4_pre_topc(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | spl6_2 ),
    inference(forward_demodulation,[],[f389,f105])).

fof(f105,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,sK2)
    | spl6_2 ),
    inference(resolution,[],[f101,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f101,plain,
    ( r1_tarski(sK4(k1_xboole_0,sK2),k1_xboole_0)
    | spl6_2 ),
    inference(resolution,[],[f98,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r1_tarski(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

% (11031)Refutation not found, incomplete strategy% (11031)------------------------------
% (11031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11031)Termination reason: Refutation not found, incomplete strategy

% (11031)Memory used [KB]: 6268
% (11031)Time elapsed: 0.138 s
% (11031)------------------------------
% (11031)------------------------------
fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
              | ~ v4_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(sK4(X0,X1),X0)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ( k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4
              & v4_pre_topc(sK5(X0,X1,X4),X1)
              & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f41,f43,f42])).

% (11042)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
              | ~ v4_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
            | ~ v4_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(sK4(X0,X1),X0)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v4_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4
        & v4_pre_topc(sK5(X0,X1,X4),X1)
        & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
                | ~ v4_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & r1_tarski(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
                & v4_pre_topc(X5,X1)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                & v4_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
              & v4_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f98,plain,
    ( ~ sP0(k1_xboole_0,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f389,plain,
    ( ! [X0] :
        ( k1_xboole_0 != sK4(k1_xboole_0,sK2)
        | ~ v4_pre_topc(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | spl6_2 ),
    inference(forward_demodulation,[],[f388,f255])).

fof(f255,plain,(
    ! [X0,X1] : k1_xboole_0 = k9_subset_1(X0,k1_xboole_0,X1) ),
    inference(resolution,[],[f166,f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f166,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4))
      | k1_xboole_0 = k9_subset_1(X4,k1_xboole_0,X5) ) ),
    inference(superposition,[],[f164,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f164,plain,(
    ! [X2,X3] : k1_xboole_0 = k9_subset_1(X2,X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f163,f119])).

fof(f119,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f109,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f67,f69])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f109,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f75,f53])).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f70,f71,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f163,plain,(
    ! [X2,X3] : k9_subset_1(X2,X3,k1_xboole_0) = k4_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f162,f53])).

fof(f162,plain,(
    ! [X2,X3] : k9_subset_1(X2,X3,k1_xboole_0) = k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)) ),
    inference(resolution,[],[f76,f52])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f72,f71])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f388,plain,
    ( ! [X0] :
        ( sK4(k1_xboole_0,sK2) != k9_subset_1(u1_struct_0(sK2),k1_xboole_0,X0)
        | ~ v4_pre_topc(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | spl6_2 ),
    inference(resolution,[],[f65,f98])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f104,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f94,f52])).

fof(f94,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_1
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f99,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f90,f96,f92])).

fof(f90,plain,
    ( ~ sP0(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f88,f81])).

fof(f81,plain,(
    ~ v2_tex_2(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f50,f78])).

fof(f78,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f55,f48])).

fof(f48,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f50,plain,(
    ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,(
    ! [X0] :
      ( v2_tex_2(X0,sK2)
      | ~ sP0(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f87,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f87,plain,(
    ! [X0] :
      ( sP1(sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f66,f47])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f25,f34,f33])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:13:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (11030)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (11031)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (11039)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (11029)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (11055)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (11051)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (11034)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (11028)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (11044)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (11049)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (11046)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (11044)Refutation not found, incomplete strategy% (11044)------------------------------
% 0.21/0.54  % (11044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11044)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11044)Memory used [KB]: 10618
% 0.21/0.54  % (11044)Time elapsed: 0.113 s
% 0.21/0.54  % (11044)------------------------------
% 0.21/0.54  % (11044)------------------------------
% 0.21/0.54  % (11041)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (11027)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (11045)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (11043)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (11033)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (11040)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (11032)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (11036)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (11053)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (11049)Refutation not found, incomplete strategy% (11049)------------------------------
% 0.21/0.55  % (11049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11049)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11049)Memory used [KB]: 10746
% 0.21/0.55  % (11049)Time elapsed: 0.091 s
% 0.21/0.55  % (11049)------------------------------
% 0.21/0.55  % (11049)------------------------------
% 0.21/0.55  % (11052)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (11037)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (11047)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (11056)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (11050)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (11035)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (11039)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f430,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f99,f104,f406,f408,f410,f420,f423,f429])).
% 0.21/0.55  fof(f429,plain,(
% 0.21/0.55    spl6_7),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f428])).
% 0.21/0.55  fof(f428,plain,(
% 0.21/0.55    $false | spl6_7),
% 0.21/0.55    inference(resolution,[],[f419,f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f54,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.55  fof(f419,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | spl6_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f417])).
% 0.21/0.55  fof(f417,plain,(
% 0.21/0.55    spl6_7 <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.55  fof(f423,plain,(
% 0.21/0.55    spl6_6),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f422])).
% 0.21/0.55  fof(f422,plain,(
% 0.21/0.55    $false | spl6_6),
% 0.21/0.55    inference(resolution,[],[f421,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    l1_pre_topc(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f37,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) => (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.21/0.55    inference(negated_conjecture,[],[f17])).
% 0.21/0.55  fof(f17,conjecture,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.21/0.55  fof(f421,plain,(
% 0.21/0.55    ~l1_pre_topc(sK2) | spl6_6),
% 0.21/0.55    inference(resolution,[],[f415,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.55  fof(f415,plain,(
% 0.21/0.55    ~l1_struct_0(sK2) | spl6_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f413])).
% 0.21/0.55  fof(f413,plain,(
% 0.21/0.55    spl6_6 <=> l1_struct_0(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.55  fof(f420,plain,(
% 0.21/0.55    ~spl6_6 | ~spl6_7 | spl6_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f411,f403,f417,f413])).
% 0.21/0.55  fof(f403,plain,(
% 0.21/0.55    spl6_5 <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.55  fof(f411,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_struct_0(sK2) | spl6_5),
% 0.21/0.55    inference(superposition,[],[f405,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.55  fof(f405,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | spl6_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f403])).
% 0.21/0.55  fof(f410,plain,(
% 0.21/0.55    spl6_4),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f409])).
% 0.21/0.55  fof(f409,plain,(
% 0.21/0.55    $false | spl6_4),
% 0.21/0.55    inference(resolution,[],[f401,f47])).
% 0.21/0.55  fof(f401,plain,(
% 0.21/0.55    ~l1_pre_topc(sK2) | spl6_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f399])).
% 0.21/0.55  fof(f399,plain,(
% 0.21/0.55    spl6_4 <=> l1_pre_topc(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.55  fof(f408,plain,(
% 0.21/0.55    spl6_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f407])).
% 0.21/0.55  fof(f407,plain,(
% 0.21/0.55    $false | spl6_3),
% 0.21/0.55    inference(resolution,[],[f397,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    v2_pre_topc(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f397,plain,(
% 0.21/0.55    ~v2_pre_topc(sK2) | spl6_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f395])).
% 0.21/0.55  fof(f395,plain,(
% 0.21/0.55    spl6_3 <=> v2_pre_topc(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.55  fof(f406,plain,(
% 0.21/0.55    ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f392,f96,f403,f399,f395])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    spl6_2 <=> sP0(k1_xboole_0,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.55  fof(f392,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl6_2),
% 0.21/0.55    inference(resolution,[],[f391,f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.21/0.55  fof(f391,plain,(
% 0.21/0.55    ( ! [X0] : (~v4_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | spl6_2),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f390])).
% 0.21/0.55  fof(f390,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~v4_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | spl6_2),
% 0.21/0.55    inference(forward_demodulation,[],[f389,f105])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    k1_xboole_0 = sK4(k1_xboole_0,sK2) | spl6_2),
% 0.21/0.55    inference(resolution,[],[f101,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    r1_tarski(sK4(k1_xboole_0,sK2),k1_xboole_0) | spl6_2),
% 0.21/0.55    inference(resolution,[],[f98,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0,X1] : (sP0(X0,X1) | r1_tarski(sK4(X0,X1),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  % (11031)Refutation not found, incomplete strategy% (11031)------------------------------
% 0.21/0.55  % (11031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11031)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11031)Memory used [KB]: 6268
% 0.21/0.55  % (11031)Time elapsed: 0.138 s
% 0.21/0.55  % (11031)------------------------------
% 0.21/0.55  % (11031)------------------------------
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X1) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f41,f43,f42])).
% 0.21/0.55  % (11042)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v4_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X1) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v4_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    ~sP0(k1_xboole_0,sK2) | spl6_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f96])).
% 0.21/0.55  fof(f389,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 != sK4(k1_xboole_0,sK2) | ~v4_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | spl6_2),
% 0.21/0.55    inference(forward_demodulation,[],[f388,f255])).
% 0.21/0.55  fof(f255,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 = k9_subset_1(X0,k1_xboole_0,X1)) )),
% 0.21/0.55    inference(resolution,[],[f166,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    ( ! [X4,X5] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4)) | k1_xboole_0 = k9_subset_1(X4,k1_xboole_0,X5)) )),
% 0.21/0.55    inference(superposition,[],[f164,f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    ( ! [X2,X3] : (k1_xboole_0 = k9_subset_1(X2,X3,k1_xboole_0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f163,f119])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f109,f84])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(resolution,[],[f67,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)) )),
% 0.21/0.55    inference(superposition,[],[f75,f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f70,f71,f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.55  fof(f163,plain,(
% 0.21/0.55    ( ! [X2,X3] : (k9_subset_1(X2,X3,k1_xboole_0) = k4_xboole_0(X3,X3)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f162,f53])).
% 0.21/0.55  fof(f162,plain,(
% 0.21/0.55    ( ! [X2,X3] : (k9_subset_1(X2,X3,k1_xboole_0) = k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0))) )),
% 0.21/0.55    inference(resolution,[],[f76,f52])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f72,f71])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.55  fof(f388,plain,(
% 0.21/0.55    ( ! [X0] : (sK4(k1_xboole_0,sK2) != k9_subset_1(u1_struct_0(sK2),k1_xboole_0,X0) | ~v4_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | spl6_2),
% 0.21/0.55    inference(resolution,[],[f65,f98])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (sP0(X0,X1) | k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    spl6_1),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f102])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    $false | spl6_1),
% 0.21/0.55    inference(resolution,[],[f94,f52])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) | spl6_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f92])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    spl6_1 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ~spl6_1 | ~spl6_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f90,f96,f92])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ~sP0(k1_xboole_0,sK2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    inference(resolution,[],[f88,f81])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ~v2_tex_2(k1_xboole_0,sK2)),
% 0.21/0.55    inference(backward_demodulation,[],[f50,f78])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    k1_xboole_0 = sK3),
% 0.21/0.55    inference(resolution,[],[f55,f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    v1_xboole_0(sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ~v2_tex_2(sK3,sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X0] : (v2_tex_2(X0,sK2) | ~sP0(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.55    inference(resolution,[],[f87,f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v2_tex_2(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ! [X0,X1] : (((v2_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1] : ((v2_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    ( ! [X0] : (sP1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.55    inference(resolution,[],[f66,f47])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(definition_folding,[],[f25,f34,f33])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (11039)------------------------------
% 0.21/0.55  % (11039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11039)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (11039)Memory used [KB]: 6396
% 0.21/0.55  % (11039)Time elapsed: 0.110 s
% 0.21/0.55  % (11039)------------------------------
% 0.21/0.55  % (11039)------------------------------
% 0.21/0.56  % (11018)Success in time 0.192 s
%------------------------------------------------------------------------------
