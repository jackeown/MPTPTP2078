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
% DateTime   : Thu Dec  3 13:22:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  132 (1926 expanded)
%              Number of leaves         :   16 ( 510 expanded)
%              Depth                    :   33
%              Number of atoms          :  531 (14855 expanded)
%              Number of equality atoms :   77 ( 359 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f346,plain,(
    $false ),
    inference(subsumption_resolution,[],[f329,f51])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f329,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f47,f328])).

fof(f328,plain,(
    k1_xboole_0 = sK3 ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK3 ),
    inference(backward_demodulation,[],[f213,f319])).

fof(f319,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f266,f318])).

fof(f318,plain,(
    k1_xboole_0 = sK4(sK3,sK2) ),
    inference(subsumption_resolution,[],[f317,f132])).

fof(f132,plain,(
    ~ sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f104,f130])).

fof(f130,plain,(
    ~ v3_tex_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f50,f129])).

fof(f129,plain,(
    v1_zfmisc_1(sK3) ),
    inference(subsumption_resolution,[],[f128,f48])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ v1_zfmisc_1(sK3)
      | ~ v3_tex_2(sK3,sK2) )
    & ( v1_zfmisc_1(sK3)
      | v3_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & ~ v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v3_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,sK2) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v3_tex_2(X1,sK2) )
        & ( v1_zfmisc_1(X1)
          | v3_tex_2(X1,sK2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK3)
        | ~ v3_tex_2(sK3,sK2) )
      & ( v1_zfmisc_1(sK3)
        | v3_tex_2(sK3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

fof(f128,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_zfmisc_1(sK3) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_zfmisc_1(sK3)
    | v1_zfmisc_1(sK3) ),
    inference(resolution,[],[f125,f108])).

fof(f108,plain,
    ( v2_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(resolution,[],[f106,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK4(X0,X1) != X0
          & r1_tarski(X0,sK4(X0,X1))
          & v2_tex_2(sK4(X0,X1),X1)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK4(X0,X1) != X0
        & r1_tarski(X0,sK4(X0,X1))
        & v2_tex_2(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ v2_tex_2(X1,X0) )
      & ( ( ! [X2] :
              ( X1 = X2
              | ~ r1_tarski(X1,X2)
              | ~ v2_tex_2(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v2_tex_2(X1,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ v2_tex_2(X1,X0) )
      & ( ( ! [X2] :
              ( X1 = X2
              | ~ r1_tarski(X1,X2)
              | ~ v2_tex_2(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v2_tex_2(X1,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f106,plain,
    ( sP0(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(resolution,[],[f105,f49])).

fof(f49,plain,
    ( v3_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f105,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | sP0(sK3,sK2) ),
    inference(resolution,[],[f103,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v3_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f26])).

% (31402)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f26,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f103,plain,(
    sP1(sK2,sK3) ),
    inference(resolution,[],[f102,f48])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f62,f46])).

fof(f46,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f26,f25])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

% (31401)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f125,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f124,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_zfmisc_1(X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f123,f46])).

fof(f123,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | v1_zfmisc_1(X0)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f77,f45])).

fof(f45,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_tdlat_3(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_zfmisc_1(X1)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f76,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f64,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_zfmisc_1(X1) )
            & ( v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f50,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f104,plain,
    ( ~ sP0(sK3,sK2)
    | v3_tex_2(sK3,sK2) ),
    inference(resolution,[],[f103,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f317,plain,
    ( sP0(sK3,sK2)
    | k1_xboole_0 = sK4(sK3,sK2) ),
    inference(subsumption_resolution,[],[f316,f265])).

fof(f265,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f264,f47])).

fof(f264,plain,
    ( v1_xboole_0(sK3)
    | v2_tex_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f262,f129])).

fof(f262,plain,
    ( ~ v1_zfmisc_1(sK3)
    | v1_xboole_0(sK3)
    | v2_tex_2(sK3,sK2) ),
    inference(resolution,[],[f261,f48])).

fof(f261,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | v2_tex_2(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f260,f43])).

fof(f260,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_xboole_0(X0)
      | v2_tex_2(X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f259,f46])).

fof(f259,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK2)
      | v2_tex_2(X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f75,f45])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_tdlat_3(X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f65,f53])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f316,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | sP0(sK3,sK2)
    | k1_xboole_0 = sK4(sK3,sK2) ),
    inference(subsumption_resolution,[],[f309,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f309,plain,
    ( ~ r1_tarski(sK3,sK3)
    | ~ v2_tex_2(sK3,sK2)
    | sP0(sK3,sK2)
    | k1_xboole_0 = sK4(sK3,sK2) ),
    inference(superposition,[],[f115,f297])).

fof(f297,plain,
    ( sK3 = sK4(sK3,sK2)
    | k1_xboole_0 = sK4(sK3,sK2) ),
    inference(resolution,[],[f295,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f72,f51])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f295,plain,
    ( v1_xboole_0(sK4(sK3,sK2))
    | sK3 = sK4(sK3,sK2) ),
    inference(subsumption_resolution,[],[f294,f265])).

fof(f294,plain,
    ( sK3 = sK4(sK3,sK2)
    | v1_xboole_0(sK4(sK3,sK2))
    | ~ v2_tex_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f293,f132])).

fof(f293,plain,
    ( sK3 = sK4(sK3,sK2)
    | v1_xboole_0(sK4(sK3,sK2))
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f286,f47])).

fof(f286,plain,
    ( sK3 = sK4(sK3,sK2)
    | v1_xboole_0(sK4(sK3,sK2))
    | v1_xboole_0(sK3)
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(resolution,[],[f285,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK4(X0,X1))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f285,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK4(sK3,sK2))
      | sK4(sK3,sK2) = X2
      | v1_xboole_0(sK4(sK3,sK2))
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f284,f132])).

fof(f284,plain,(
    ! [X2] :
      ( sP0(sK3,sK2)
      | ~ r1_tarski(X2,sK4(sK3,sK2))
      | sK4(sK3,sK2) = X2
      | v1_xboole_0(sK4(sK3,sK2))
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f143,f265])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X0,sK2)
      | sP0(X0,sK2)
      | ~ r1_tarski(X1,sK4(X0,sK2))
      | sK4(X0,sK2) = X1
      | v1_xboole_0(sK4(X0,sK2))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f133,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f133,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK4(X0,sK2))
      | sP0(X0,sK2)
      | ~ v2_tex_2(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f127,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f127,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_zfmisc_1(sK4(X0,sK2))
      | sP0(X0,sK2)
      | ~ v2_tex_2(X0,sK2) ) ),
    inference(resolution,[],[f125,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK4(X0,X1),X1)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4(X0,X1),X0)
      | ~ v2_tex_2(X0,X1)
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f113,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f113,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | ~ r1_tarski(sK4(X0,X1),X0)
      | sK4(X0,X1) = X0 ) ),
    inference(resolution,[],[f60,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f266,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f131,f265])).

fof(f131,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f121,f130])).

fof(f121,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2))
    | v3_tex_2(sK3,sK2) ),
    inference(resolution,[],[f114,f104])).

fof(f114,plain,(
    ! [X2,X3] :
      ( sP0(X2,X3)
      | ~ v2_tex_2(X2,X3)
      | k1_xboole_0 = k4_xboole_0(X2,sK4(X2,X3)) ) ),
    inference(resolution,[],[f60,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f213,plain,
    ( sK3 = k4_xboole_0(sK3,k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f210,f98])).

fof(f98,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f69,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(superposition,[],[f66,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f71,f73])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f210,plain,(
    ! [X0] :
      ( r1_tarski(sK3,X0)
      | sK3 = k4_xboole_0(sK3,X0) ) ),
    inference(condensation,[],[f209])).

fof(f209,plain,(
    ! [X8,X9] :
      ( r1_tarski(sK3,X8)
      | sK3 = k4_xboole_0(sK3,X8)
      | sK3 = k4_xboole_0(sK3,X9) ) ),
    inference(subsumption_resolution,[],[f173,f140])).

fof(f140,plain,(
    ! [X0] :
      ( sK3 = k4_xboole_0(sK3,X0)
      | k1_xboole_0 = k4_xboole_0(sK3,X0) ) ),
    inference(resolution,[],[f138,f79])).

fof(f138,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_xboole_0(sK3,X0))
      | sK3 = k4_xboole_0(sK3,X0) ) ),
    inference(resolution,[],[f135,f66])).

fof(f135,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3)
      | sK3 = X0
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f134,f47])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3)
      | sK3 = X0
      | v1_xboole_0(sK3)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f129,f52])).

fof(f173,plain,(
    ! [X8,X9] :
      ( k1_xboole_0 != k4_xboole_0(sK3,X9)
      | r1_tarski(sK3,X8)
      | sK3 = k4_xboole_0(sK3,X8)
      | sK3 = k4_xboole_0(sK3,X9) ) ),
    inference(superposition,[],[f70,f157])).

fof(f157,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(sK3,X1) = k4_xboole_0(sK3,X2)
      | sK3 = k4_xboole_0(sK3,X1)
      | sK3 = k4_xboole_0(sK3,X2) ) ),
    inference(resolution,[],[f141,f138])).

fof(f141,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | k4_xboole_0(sK3,X1) = X2
      | sK3 = k4_xboole_0(sK3,X1) ) ),
    inference(resolution,[],[f138,f72])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f47,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:51:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (31420)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (31424)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (31407)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (31423)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (31414)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (31416)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (31413)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (31421)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (31406)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (31404)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (31408)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (31415)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (31405)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (31404)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (31405)Refutation not found, incomplete strategy% (31405)------------------------------
% 0.22/0.53  % (31405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31405)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31405)Memory used [KB]: 6140
% 0.22/0.53  % (31405)Time elapsed: 0.102 s
% 0.22/0.53  % (31405)------------------------------
% 0.22/0.53  % (31405)------------------------------
% 0.22/0.53  % (31408)Refutation not found, incomplete strategy% (31408)------------------------------
% 0.22/0.53  % (31408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31408)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31408)Memory used [KB]: 1663
% 0.22/0.53  % (31408)Time elapsed: 0.067 s
% 0.22/0.53  % (31408)------------------------------
% 0.22/0.53  % (31408)------------------------------
% 0.22/0.53  % (31412)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (31407)Refutation not found, incomplete strategy% (31407)------------------------------
% 0.22/0.53  % (31407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31422)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (31407)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31407)Memory used [KB]: 10618
% 0.22/0.53  % (31407)Time elapsed: 0.104 s
% 0.22/0.53  % (31407)------------------------------
% 0.22/0.53  % (31407)------------------------------
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f346,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f329,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.54  fof(f329,plain,(
% 0.22/0.54    ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(backward_demodulation,[],[f47,f328])).
% 0.22/0.54  fof(f328,plain,(
% 0.22/0.54    k1_xboole_0 = sK3),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f327])).
% 0.22/0.54  fof(f327,plain,(
% 0.22/0.54    k1_xboole_0 = sK3 | k1_xboole_0 = sK3),
% 0.22/0.54    inference(backward_demodulation,[],[f213,f319])).
% 0.22/0.54  fof(f319,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK3,k1_xboole_0)),
% 0.22/0.54    inference(backward_demodulation,[],[f266,f318])).
% 0.22/0.54  fof(f318,plain,(
% 0.22/0.54    k1_xboole_0 = sK4(sK3,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f317,f132])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    ~sP0(sK3,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f104,f130])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    ~v3_tex_2(sK3,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f50,f129])).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    v1_zfmisc_1(sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f128,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f31,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_zfmisc_1(sK3)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f126])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_zfmisc_1(sK3) | v1_zfmisc_1(sK3)),
% 0.22/0.54    inference(resolution,[],[f125,f108])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    v2_tex_2(sK3,sK2) | v1_zfmisc_1(sK3)),
% 0.22/0.54    inference(resolution,[],[f106,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~sP0(X0,X1) | v2_tex_2(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1] : ((sP0(X0,X1) | (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 0.22/0.54    inference(flattening,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    sP0(sK3,sK2) | v1_zfmisc_1(sK3)),
% 0.22/0.54    inference(resolution,[],[f105,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    v3_tex_2(sK3,sK2) | v1_zfmisc_1(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ~v3_tex_2(sK3,sK2) | sP0(sK3,sK2)),
% 0.22/0.54    inference(resolution,[],[f103,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~sP1(X0,X1) | ~v3_tex_2(X1,X0) | sP0(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : (((v3_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f26])).
% 0.22/0.54  % (31402)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : ((v3_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    sP1(sK2,sK3)),
% 0.22/0.54    inference(resolution,[],[f102,f48])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 0.22/0.54    inference(resolution,[],[f62,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    l1_pre_topc(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(definition_folding,[],[f20,f26,f25])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  % (31401)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_tex_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v1_zfmisc_1(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f124,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ~v2_struct_0(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_tex_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v1_zfmisc_1(X0) | v2_struct_0(sK2)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f123,f46])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_tex_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | v1_zfmisc_1(X0) | v2_struct_0(sK2)) )),
% 0.22/0.54    inference(resolution,[],[f77,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    v2_tdlat_3(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v2_tdlat_3(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_zfmisc_1(X1) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f76,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f64,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ~v3_tex_2(sK3,sK2) | ~v1_zfmisc_1(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ~sP0(sK3,sK2) | v3_tex_2(sK3,sK2)),
% 0.22/0.54    inference(resolution,[],[f103,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v3_tex_2(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f317,plain,(
% 0.22/0.54    sP0(sK3,sK2) | k1_xboole_0 = sK4(sK3,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f316,f265])).
% 0.22/0.54  fof(f265,plain,(
% 0.22/0.54    v2_tex_2(sK3,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f264,f47])).
% 0.22/0.54  fof(f264,plain,(
% 0.22/0.54    v1_xboole_0(sK3) | v2_tex_2(sK3,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f262,f129])).
% 0.22/0.54  fof(f262,plain,(
% 0.22/0.54    ~v1_zfmisc_1(sK3) | v1_xboole_0(sK3) | v2_tex_2(sK3,sK2)),
% 0.22/0.54    inference(resolution,[],[f261,f48])).
% 0.22/0.54  fof(f261,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0) | v2_tex_2(X0,sK2)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f260,f43])).
% 0.22/0.54  fof(f260,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_zfmisc_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X0) | v2_tex_2(X0,sK2) | v2_struct_0(sK2)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f259,f46])).
% 0.22/0.54  fof(f259,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_zfmisc_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X0) | ~l1_pre_topc(sK2) | v2_tex_2(X0,sK2) | v2_struct_0(sK2)) )),
% 0.22/0.54    inference(resolution,[],[f75,f45])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v2_tdlat_3(X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f65,f53])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f316,plain,(
% 0.22/0.54    ~v2_tex_2(sK3,sK2) | sP0(sK3,sK2) | k1_xboole_0 = sK4(sK3,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f309,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f309,plain,(
% 0.22/0.54    ~r1_tarski(sK3,sK3) | ~v2_tex_2(sK3,sK2) | sP0(sK3,sK2) | k1_xboole_0 = sK4(sK3,sK2)),
% 0.22/0.54    inference(superposition,[],[f115,f297])).
% 0.22/0.54  fof(f297,plain,(
% 0.22/0.54    sK3 = sK4(sK3,sK2) | k1_xboole_0 = sK4(sK3,sK2)),
% 0.22/0.54    inference(resolution,[],[f295,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(resolution,[],[f72,f51])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.54  fof(f295,plain,(
% 0.22/0.54    v1_xboole_0(sK4(sK3,sK2)) | sK3 = sK4(sK3,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f294,f265])).
% 0.22/0.54  fof(f294,plain,(
% 0.22/0.54    sK3 = sK4(sK3,sK2) | v1_xboole_0(sK4(sK3,sK2)) | ~v2_tex_2(sK3,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f293,f132])).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    sK3 = sK4(sK3,sK2) | v1_xboole_0(sK4(sK3,sK2)) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f286,f47])).
% 0.22/0.54  fof(f286,plain,(
% 0.22/0.54    sK3 = sK4(sK3,sK2) | v1_xboole_0(sK4(sK3,sK2)) | v1_xboole_0(sK3) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.22/0.54    inference(resolution,[],[f285,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,sK4(X0,X1)) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f285,plain,(
% 0.22/0.54    ( ! [X2] : (~r1_tarski(X2,sK4(sK3,sK2)) | sK4(sK3,sK2) = X2 | v1_xboole_0(sK4(sK3,sK2)) | v1_xboole_0(X2)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f284,f132])).
% 0.22/0.54  fof(f284,plain,(
% 0.22/0.54    ( ! [X2] : (sP0(sK3,sK2) | ~r1_tarski(X2,sK4(sK3,sK2)) | sK4(sK3,sK2) = X2 | v1_xboole_0(sK4(sK3,sK2)) | v1_xboole_0(X2)) )),
% 0.22/0.54    inference(resolution,[],[f143,f265])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v2_tex_2(X0,sK2) | sP0(X0,sK2) | ~r1_tarski(X1,sK4(X0,sK2)) | sK4(X0,sK2) = X1 | v1_xboole_0(sK4(X0,sK2)) | v1_xboole_0(X1)) )),
% 0.22/0.54    inference(resolution,[],[f133,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    ( ! [X0] : (v1_zfmisc_1(sK4(X0,sK2)) | sP0(X0,sK2) | ~v2_tex_2(X0,sK2)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f127,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(sK2))) | v1_zfmisc_1(sK4(X0,sK2)) | sP0(X0,sK2) | ~v2_tex_2(X0,sK2)) )),
% 0.22/0.54    inference(resolution,[],[f125,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v2_tex_2(sK4(X0,X1),X1) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(sK4(X0,X1),X0) | ~v2_tex_2(X0,X1) | sP0(X0,X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f113,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sK4(X0,X1) != X0 | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sP0(X0,X1) | ~v2_tex_2(X0,X1) | ~r1_tarski(sK4(X0,X1),X0) | sK4(X0,X1) = X0) )),
% 0.22/0.54    inference(resolution,[],[f60,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f266,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f131,f265])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    ~v2_tex_2(sK3,sK2) | k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f121,f130])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    ~v2_tex_2(sK3,sK2) | k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2)) | v3_tex_2(sK3,sK2)),
% 0.22/0.54    inference(resolution,[],[f114,f104])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ( ! [X2,X3] : (sP0(X2,X3) | ~v2_tex_2(X2,X3) | k1_xboole_0 = k4_xboole_0(X2,sK4(X2,X3))) )),
% 0.22/0.54    inference(resolution,[],[f60,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.54  fof(f213,plain,(
% 0.22/0.54    sK3 = k4_xboole_0(sK3,k1_xboole_0) | k1_xboole_0 = sK3),
% 0.22/0.54    inference(resolution,[],[f210,f98])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 0.22/0.54    inference(resolution,[],[f69,f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 0.22/0.54    inference(superposition,[],[f66,f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f71,f73])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.55  fof(f210,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(sK3,X0) | sK3 = k4_xboole_0(sK3,X0)) )),
% 0.22/0.55    inference(condensation,[],[f209])).
% 0.22/0.55  fof(f209,plain,(
% 0.22/0.55    ( ! [X8,X9] : (r1_tarski(sK3,X8) | sK3 = k4_xboole_0(sK3,X8) | sK3 = k4_xboole_0(sK3,X9)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f173,f140])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    ( ! [X0] : (sK3 = k4_xboole_0(sK3,X0) | k1_xboole_0 = k4_xboole_0(sK3,X0)) )),
% 0.22/0.55    inference(resolution,[],[f138,f79])).
% 0.22/0.55  fof(f138,plain,(
% 0.22/0.55    ( ! [X0] : (v1_xboole_0(k4_xboole_0(sK3,X0)) | sK3 = k4_xboole_0(sK3,X0)) )),
% 0.22/0.55    inference(resolution,[],[f135,f66])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(X0,sK3) | sK3 = X0 | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f134,f47])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(X0,sK3) | sK3 = X0 | v1_xboole_0(sK3) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(resolution,[],[f129,f52])).
% 0.22/0.55  fof(f173,plain,(
% 0.22/0.55    ( ! [X8,X9] : (k1_xboole_0 != k4_xboole_0(sK3,X9) | r1_tarski(sK3,X8) | sK3 = k4_xboole_0(sK3,X8) | sK3 = k4_xboole_0(sK3,X9)) )),
% 0.22/0.55    inference(superposition,[],[f70,f157])).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    ( ! [X2,X1] : (k4_xboole_0(sK3,X1) = k4_xboole_0(sK3,X2) | sK3 = k4_xboole_0(sK3,X1) | sK3 = k4_xboole_0(sK3,X2)) )),
% 0.22/0.55    inference(resolution,[],[f141,f138])).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    ( ! [X2,X1] : (~v1_xboole_0(X2) | k4_xboole_0(sK3,X1) = X2 | sK3 = k4_xboole_0(sK3,X1)) )),
% 0.22/0.55    inference(resolution,[],[f138,f72])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ~v1_xboole_0(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (31404)------------------------------
% 0.22/0.55  % (31404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31404)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (31404)Memory used [KB]: 6268
% 0.22/0.55  % (31404)Time elapsed: 0.097 s
% 0.22/0.55  % (31404)------------------------------
% 0.22/0.55  % (31404)------------------------------
% 0.22/0.55  % (31400)Success in time 0.178 s
%------------------------------------------------------------------------------
