%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 170 expanded)
%              Number of leaves         :   23 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  317 ( 723 expanded)
%              Number of equality atoms :   46 (  70 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f86,f89,f114,f116,f126,f130,f135])).

fof(f135,plain,
    ( spl6_3
    | ~ spl6_2
    | ~ spl6_1
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f133,f120,f73,f77,f81])).

fof(f81,plain,
    ( spl6_3
  <=> v2_tex_2(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f77,plain,
    ( spl6_2
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f73,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK4(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f120,plain,
    ( spl6_7
  <=> ! [X0] :
        ( sP0(X0,sK2)
        | k1_xboole_0 != sK4(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f133,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(k1_xboole_0,sK2)
    | ~ spl6_1
    | ~ spl6_7 ),
    inference(resolution,[],[f132,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_tex_2(X0,sK2) ) ),
    inference(resolution,[],[f67,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f67,plain,(
    ! [X0] :
      ( sP1(sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f53,f38])).

fof(f38,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f28,f27])).

fof(f27,plain,
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

fof(f28,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v1_xboole_0(X1) )
   => ( ~ v2_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f16,f25,f24])).

fof(f24,plain,(
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f132,plain,
    ( sP0(k1_xboole_0,sK2)
    | ~ spl6_1
    | ~ spl6_7 ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sP0(k1_xboole_0,sK2)
    | ~ spl6_1
    | ~ spl6_7 ),
    inference(superposition,[],[f121,f75])).

fof(f75,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f121,plain,
    ( ! [X0] :
        ( k1_xboole_0 != sK4(X0,sK2)
        | sP0(X0,sK2) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f130,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl6_8 ),
    inference(resolution,[],[f125,f37])).

fof(f37,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f125,plain,
    ( ~ v2_pre_topc(sK2)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_8
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f126,plain,
    ( spl6_7
    | ~ spl6_8
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f118,f112,f123,f120])).

fof(f112,plain,
    ( spl6_6
  <=> ! [X1,X0] :
        ( sP0(X0,X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_xboole_0 != sK4(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK2)
        | sP0(X0,sK2)
        | k1_xboole_0 != sK4(X0,sK2) )
    | ~ spl6_6 ),
    inference(resolution,[],[f117,f38])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | sP0(X1,X0)
        | k1_xboole_0 != sK4(X1,X0) )
    | ~ spl6_6 ),
    inference(resolution,[],[f113,f43])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

% (9726)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (9742)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | sP0(X0,X1)
        | k1_xboole_0 != sK4(X0,X1) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f116,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl6_5 ),
    inference(resolution,[],[f110,f42])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f110,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f114,plain,
    ( ~ spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f106,f112,f108])).

fof(f106,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_xboole_0 != sK4(X0,X1)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f105,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(k1_xboole_0,X1)
      | sP0(X0,X1)
      | k1_xboole_0 != sK4(X0,X1) ) ),
    inference(resolution,[],[f104,f43])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X1,X0)
      | ~ v4_pre_topc(k1_xboole_0,X0)
      | k1_xboole_0 != sK4(X1,X0) ) ),
    inference(superposition,[],[f52,f100])).

fof(f100,plain,(
    ! [X0,X1] : k1_xboole_0 = k9_subset_1(X0,X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f98,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f98,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f61,f43])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f58,f57])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
      | sP0(X0,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).

fof(f33,plain,(
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

fof(f34,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v4_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4
        & v4_pre_topc(sK5(X0,X1,X4),X1)
        & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f89,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl6_3 ),
    inference(resolution,[],[f83,f66])).

fof(f66,plain,(
    ~ v2_tex_2(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f41,f62])).

fof(f62,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f54,f39])).

fof(f39,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f41,plain,(
    ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,
    ( v2_tex_2(k1_xboole_0,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f86,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl6_2 ),
    inference(resolution,[],[f79,f43])).

fof(f79,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f84,plain,
    ( spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f71,f81,f77,f73])).

fof(f71,plain,
    ( v2_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = sK4(k1_xboole_0,sK2) ),
    inference(resolution,[],[f70,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f70,plain,(
    ! [X0] :
      ( r1_tarski(sK4(X0,sK2),X0)
      | v2_tex_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f68,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r1_tarski(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:57:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (9732)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (9733)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.47  % (9732)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f84,f86,f89,f114,f116,f126,f130,f135])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    spl6_3 | ~spl6_2 | ~spl6_1 | ~spl6_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f133,f120,f73,f77,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl6_3 <=> v2_tex_2(k1_xboole_0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    spl6_2 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    spl6_1 <=> k1_xboole_0 = sK4(k1_xboole_0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    spl6_7 <=> ! [X0] : (sP0(X0,sK2) | k1_xboole_0 != sK4(X0,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tex_2(k1_xboole_0,sK2) | (~spl6_1 | ~spl6_7)),
% 0.20/0.49    inference(resolution,[],[f132,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X0] : (~sP0(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tex_2(X0,sK2)) )),
% 0.20/0.49    inference(resolution,[],[f67,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v2_tex_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1] : (((v2_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : ((v2_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X0] : (sP1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.20/0.49    inference(resolution,[],[f53,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    l1_pre_topc(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f28,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) => (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.49    inference(negated_conjecture,[],[f11])).
% 0.20/0.49  fof(f11,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(definition_folding,[],[f16,f25,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    sP0(k1_xboole_0,sK2) | (~spl6_1 | ~spl6_7)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f131])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | sP0(k1_xboole_0,sK2) | (~spl6_1 | ~spl6_7)),
% 0.20/0.49    inference(superposition,[],[f121,f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    k1_xboole_0 = sK4(k1_xboole_0,sK2) | ~spl6_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f73])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 != sK4(X0,sK2) | sP0(X0,sK2)) ) | ~spl6_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f120])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    spl6_8),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f129])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    $false | spl6_8),
% 0.20/0.49    inference(resolution,[],[f125,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    v2_pre_topc(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ~v2_pre_topc(sK2) | spl6_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f123])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    spl6_8 <=> v2_pre_topc(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    spl6_7 | ~spl6_8 | ~spl6_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f118,f112,f123,f120])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    spl6_6 <=> ! [X1,X0] : (sP0(X0,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) | k1_xboole_0 != sK4(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X0] : (~v2_pre_topc(sK2) | sP0(X0,sK2) | k1_xboole_0 != sK4(X0,sK2)) ) | ~spl6_6),
% 0.20/0.49    inference(resolution,[],[f117,f38])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | sP0(X1,X0) | k1_xboole_0 != sK4(X1,X0)) ) | ~spl6_6),
% 0.20/0.49    inference(resolution,[],[f113,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.49  % (9726)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (9742)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | sP0(X0,X1) | k1_xboole_0 != sK4(X0,X1)) ) | ~spl6_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f112])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    spl6_5),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f115])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    $false | spl6_5),
% 0.20/0.50    inference(resolution,[],[f110,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | spl6_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f108])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    spl6_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    ~spl6_5 | spl6_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f106,f112,f108])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sP0(X0,X1) | k1_xboole_0 != sK4(X0,X1) | ~v1_xboole_0(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.20/0.50    inference(resolution,[],[f105,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v4_pre_topc(k1_xboole_0,X1) | sP0(X0,X1) | k1_xboole_0 != sK4(X0,X1)) )),
% 0.20/0.50    inference(resolution,[],[f104,f43])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | sP0(X1,X0) | ~v4_pre_topc(k1_xboole_0,X0) | k1_xboole_0 != sK4(X1,X0)) )),
% 0.20/0.50    inference(superposition,[],[f52,f100])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k9_subset_1(X0,X1,k1_xboole_0)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f98,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f44,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k9_subset_1(X0,X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 0.20/0.50    inference(resolution,[],[f61,f43])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f58,f57])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | sP0(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X1) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v4_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X1) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v4_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.20/0.50    inference(rectify,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f24])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ~spl6_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    $false | ~spl6_3),
% 0.20/0.50    inference(resolution,[],[f83,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ~v2_tex_2(k1_xboole_0,sK2)),
% 0.20/0.50    inference(backward_demodulation,[],[f41,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    k1_xboole_0 = sK3),
% 0.20/0.50    inference(resolution,[],[f54,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    v1_xboole_0(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ~v2_tex_2(sK3,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    v2_tex_2(k1_xboole_0,sK2) | ~spl6_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f81])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    spl6_2),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    $false | spl6_2),
% 0.20/0.50    inference(resolution,[],[f79,f43])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) | spl6_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f77])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    spl6_1 | ~spl6_2 | spl6_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f71,f81,f77,f73])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    v2_tex_2(k1_xboole_0,sK2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_xboole_0 = sK4(k1_xboole_0,sK2)),
% 0.20/0.50    inference(resolution,[],[f70,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(sK4(X0,sK2),X0) | v2_tex_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.20/0.50    inference(resolution,[],[f68,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sP0(X0,X1) | r1_tarski(sK4(X0,X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (9732)------------------------------
% 0.20/0.50  % (9732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9732)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (9732)Memory used [KB]: 6268
% 0.20/0.50  % (9732)Time elapsed: 0.101 s
% 0.20/0.50  % (9732)------------------------------
% 0.20/0.50  % (9732)------------------------------
% 0.20/0.50  % (9718)Success in time 0.144 s
%------------------------------------------------------------------------------
