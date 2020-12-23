%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 (1998 expanded)
%              Number of leaves         :   12 ( 547 expanded)
%              Depth                    :   33
%              Number of atoms          :  427 (16187 expanded)
%              Number of equality atoms :   25 ( 121 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(subsumption_resolution,[],[f240,f182])).

fof(f182,plain,(
    sK4 != sK5(sK4,sK3) ),
    inference(resolution,[],[f172,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | sK5(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK5(X0,X1) != X0
          & r1_tarski(X0,sK5(X0,X1))
          & v2_tex_2(sK5(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK5(X0,X1) != X0
        & r1_tarski(X0,sK5(X0,X1))
        & v2_tex_2(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( X1 = X2
          | ~ r1_tarski(X1,X2)
          | ~ v2_tex_2(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f172,plain,(
    ~ sP0(sK4,sK3) ),
    inference(subsumption_resolution,[],[f164,f151])).

fof(f151,plain,(
    ~ sP1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f150,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( sP0(X1,X0)
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f150,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ sP1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f149,f117])).

fof(f117,plain,(
    sP2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f105,f42])).

fof(f42,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ v1_zfmisc_1(sK4)
      | ~ v3_tex_2(sK4,sK3) )
    & ( v1_zfmisc_1(sK4)
      | v3_tex_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & ~ v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f28,f27])).

fof(f27,plain,
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
            | ~ v3_tex_2(X1,sK3) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v3_tex_2(X1,sK3) )
        & ( v1_zfmisc_1(X1)
          | v3_tex_2(X1,sK3) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK4)
        | ~ v3_tex_2(sK4,sK3) )
      & ( v1_zfmisc_1(sK4)
        | v3_tex_2(sK4,sK3) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

fof(f105,plain,
    ( sP2(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f44,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f14,f23,f22,f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ( v3_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f29])).

fof(f149,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ sP1(sK3,sK4)
    | ~ sP2(sK4,sK3) ),
    inference(resolution,[],[f127,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X0,X1)
      | ~ sP1(X1,X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v3_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f127,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(resolution,[],[f111,f46])).

fof(f46,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f111,plain,
    ( v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f110,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f110,plain,
    ( v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f109,f40])).

fof(f40,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f109,plain,
    ( v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f108,f41])).

fof(f41,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f108,plain,
    ( v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f107,f42])).

fof(f107,plain,
    ( v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f103,f43])).

fof(f43,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f29])).

% (22808)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f103,plain,
    ( v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3)
    | v1_xboole_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f44,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f164,plain,
    ( sP1(sK3,sK4)
    | ~ sP0(sK4,sK3) ),
    inference(resolution,[],[f156,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ sP0(X1,X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f156,plain,(
    v2_tex_2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f133,f154])).

fof(f154,plain,(
    ~ v3_tex_2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f153,f117])).

fof(f153,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ sP2(sK4,sK3) ),
    inference(resolution,[],[f151,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ v3_tex_2(X0,X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f133,plain,
    ( v2_tex_2(sK4,sK3)
    | v3_tex_2(sK4,sK3) ),
    inference(resolution,[],[f116,f45])).

fof(f45,plain,
    ( v1_zfmisc_1(sK4)
    | v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f116,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f115,f39])).

fof(f115,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f114,f40])).

fof(f114,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f113,f41])).

fof(f113,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f112,f42])).

fof(f112,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f104,f43])).

fof(f104,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4)
    | v1_xboole_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f44,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f240,plain,(
    sK4 = sK5(sK4,sK3) ),
    inference(subsumption_resolution,[],[f237,f181])).

fof(f181,plain,(
    r1_tarski(sK4,sK5(sK4,sK3)) ),
    inference(resolution,[],[f172,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r1_tarski(X0,sK5(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f237,plain,
    ( ~ r1_tarski(sK4,sK5(sK4,sK3))
    | sK4 = sK5(sK4,sK3) ),
    inference(resolution,[],[f234,f191])).

fof(f191,plain,(
    ! [X3] :
      ( ~ v1_zfmisc_1(X3)
      | ~ r1_tarski(sK4,X3)
      | sK4 = X3 ) ),
    inference(subsumption_resolution,[],[f94,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f91,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f91,plain,(
    ! [X0] : ~ v1_xboole_0(k2_xboole_0(sK4,X0)) ),
    inference(resolution,[],[f43,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_xboole_0)).

fof(f94,plain,(
    ! [X3] :
      ( sK4 = X3
      | ~ r1_tarski(sK4,X3)
      | ~ v1_zfmisc_1(X3)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f43,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f234,plain,(
    v1_zfmisc_1(sK5(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f233,f39])).

fof(f233,plain,
    ( v1_zfmisc_1(sK5(sK4,sK3))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f232,f40])).

fof(f232,plain,
    ( v1_zfmisc_1(sK5(sK4,sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f231,f41])).

fof(f231,plain,
    ( v1_zfmisc_1(sK5(sK4,sK3))
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f230,f42])).

fof(f230,plain,
    ( v1_zfmisc_1(sK5(sK4,sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f229,f192])).

fof(f192,plain,(
    ~ v1_xboole_0(sK5(sK4,sK3)) ),
    inference(resolution,[],[f181,f101])).

fof(f229,plain,
    ( v1_zfmisc_1(sK5(sK4,sK3))
    | v1_xboole_0(sK5(sK4,sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f225,f180])).

fof(f180,plain,(
    v2_tex_2(sK5(sK4,sK3),sK3) ),
    inference(resolution,[],[f172,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v2_tex_2(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f225,plain,
    ( v1_zfmisc_1(sK5(sK4,sK3))
    | ~ v2_tex_2(sK5(sK4,sK3),sK3)
    | v1_xboole_0(sK5(sK4,sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f179,f59])).

fof(f179,plain,(
    m1_subset_1(sK5(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f172,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:43:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (22816)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.48  % (22816)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (22815)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.48  % (22809)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.48  % (22826)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.48  % (22828)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.48  % (22825)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.48  % (22810)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.48  % (22813)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f240,f182])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    sK4 != sK5(sK4,sK3)),
% 0.21/0.48    inference(resolution,[],[f172,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP0(X0,X1) | sK5(X0,X1) != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP0(X0,X1) | (sK5(X0,X1) != X0 & r1_tarski(X0,sK5(X0,X1)) & v2_tex_2(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK5(X0,X1) != X0 & r1_tarski(X0,sK5(X0,X1)) & v2_tex_2(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    ~sP0(sK4,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f164,f151])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ~sP1(sK3,sK4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f150,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~sP1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.21/0.48    inference(flattening,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(X1,X0) | ~v2_tex_2(X1,X0))) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (sP1(X0,X1) <=> (sP0(X1,X0) & v2_tex_2(X1,X0)))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ~v2_tex_2(sK4,sK3) | ~sP1(sK3,sK4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f149,f117])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    sP2(sK4,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    l1_pre_topc(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ((~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f28,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    sP2(sK4,sK3) | ~l1_pre_topc(sK3)),
% 0.21/0.48    inference(resolution,[],[f44,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(definition_folding,[],[f14,f23,f22,f21])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X1,X0] : ((v3_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ~v2_tex_2(sK4,sK3) | ~sP1(sK3,sK4) | ~sP2(sK4,sK3)),
% 0.21/0.48    inference(resolution,[],[f127,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v3_tex_2(X0,X1) | ~sP1(X1,X0) | ~sP2(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : (((v3_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v3_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 0.21/0.48    inference(rectify,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X1,X0] : (((v3_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v3_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f23])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ~v3_tex_2(sK4,sK3) | ~v2_tex_2(sK4,sK3)),
% 0.21/0.48    inference(resolution,[],[f111,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f110,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ~v2_struct_0(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3) | v2_struct_0(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f109,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v2_pre_topc(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f108,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    v2_tdlat_3(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f107,f42])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f103,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ~v1_xboole_0(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  % (22808)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3) | v1_xboole_0(sK4) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.48    inference(resolution,[],[f44,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    sP1(sK3,sK4) | ~sP0(sK4,sK3)),
% 0.21/0.48    inference(resolution,[],[f156,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    v2_tex_2(sK4,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f154])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ~v3_tex_2(sK4,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f153,f117])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ~v3_tex_2(sK4,sK3) | ~sP2(sK4,sK3)),
% 0.21/0.48    inference(resolution,[],[f151,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP1(X1,X0) | ~v3_tex_2(X0,X1) | ~sP2(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    v2_tex_2(sK4,sK3) | v3_tex_2(sK4,sK3)),
% 0.21/0.48    inference(resolution,[],[f116,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f39])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    v2_tex_2(sK4,sK3) | ~v1_zfmisc_1(sK4) | v2_struct_0(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f40])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    v2_tex_2(sK4,sK3) | ~v1_zfmisc_1(sK4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f113,f41])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    v2_tex_2(sK4,sK3) | ~v1_zfmisc_1(sK4) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f112,f42])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    v2_tex_2(sK4,sK3) | ~v1_zfmisc_1(sK4) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f104,f43])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    v2_tex_2(sK4,sK3) | ~v1_zfmisc_1(sK4) | v1_xboole_0(sK4) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.48    inference(resolution,[],[f44,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    sK4 = sK5(sK4,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f237,f181])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    r1_tarski(sK4,sK5(sK4,sK3))),
% 0.21/0.48    inference(resolution,[],[f172,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP0(X0,X1) | r1_tarski(X0,sK5(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    ~r1_tarski(sK4,sK5(sK4,sK3)) | sK4 = sK5(sK4,sK3)),
% 0.21/0.48    inference(resolution,[],[f234,f191])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ( ! [X3] : (~v1_zfmisc_1(X3) | ~r1_tarski(sK4,X3) | sK4 = X3) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f94,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK4,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(superposition,[],[f91,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(k2_xboole_0(sK4,X0))) )),
% 0.21/0.48    inference(resolution,[],[f43,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X0,X1)) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X0,X1)) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X0) => ~v1_xboole_0(k2_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_xboole_0)).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X3] : (sK4 = X3 | ~r1_tarski(sK4,X3) | ~v1_zfmisc_1(X3) | v1_xboole_0(X3)) )),
% 0.21/0.48    inference(resolution,[],[f43,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    v1_zfmisc_1(sK5(sK4,sK3))),
% 0.21/0.48    inference(subsumption_resolution,[],[f233,f39])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    v1_zfmisc_1(sK5(sK4,sK3)) | v2_struct_0(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f232,f40])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    v1_zfmisc_1(sK5(sK4,sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f231,f41])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    v1_zfmisc_1(sK5(sK4,sK3)) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f230,f42])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    v1_zfmisc_1(sK5(sK4,sK3)) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f229,f192])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    ~v1_xboole_0(sK5(sK4,sK3))),
% 0.21/0.48    inference(resolution,[],[f181,f101])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    v1_zfmisc_1(sK5(sK4,sK3)) | v1_xboole_0(sK5(sK4,sK3)) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f225,f180])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    v2_tex_2(sK5(sK4,sK3),sK3)),
% 0.21/0.48    inference(resolution,[],[f172,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP0(X0,X1) | v2_tex_2(sK5(X0,X1),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    v1_zfmisc_1(sK5(sK4,sK3)) | ~v2_tex_2(sK5(sK4,sK3),sK3) | v1_xboole_0(sK5(sK4,sK3)) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.48    inference(resolution,[],[f179,f59])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    m1_subset_1(sK5(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.48    inference(resolution,[],[f172,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (22816)------------------------------
% 0.21/0.48  % (22816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22816)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (22816)Memory used [KB]: 1663
% 0.21/0.48  % (22816)Time elapsed: 0.080 s
% 0.21/0.48  % (22816)------------------------------
% 0.21/0.48  % (22816)------------------------------
% 0.21/0.49  % (22807)Success in time 0.127 s
%------------------------------------------------------------------------------
