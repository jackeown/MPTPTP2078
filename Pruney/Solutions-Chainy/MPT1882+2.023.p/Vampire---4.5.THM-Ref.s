%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:03 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  114 (2362 expanded)
%              Number of leaves         :   16 ( 647 expanded)
%              Depth                    :   36
%              Number of atoms          :  464 (19097 expanded)
%              Number of equality atoms :   37 ( 153 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f277])).

fof(f277,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f269,f276])).

fof(f276,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(sK5(sK4,sK3),X0) ),
    inference(resolution,[],[f275,f72])).

fof(f72,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f275,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK4,sK3)))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f273,f71])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f273,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK4,sK3))) ) ),
    inference(resolution,[],[f272,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f272,plain,(
    v1_xboole_0(sK5(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f271,f224])).

fof(f224,plain,(
    v1_zfmisc_1(sK5(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f223,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f223,plain,
    ( v1_zfmisc_1(sK5(sK4,sK3))
    | v1_xboole_0(sK5(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f222,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f222,plain,
    ( v1_zfmisc_1(sK5(sK4,sK3))
    | v1_xboole_0(sK5(sK4,sK3))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f221,f48])).

fof(f48,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f221,plain,
    ( v1_zfmisc_1(sK5(sK4,sK3))
    | v1_xboole_0(sK5(sK4,sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f220,f49])).

fof(f49,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f220,plain,
    ( v1_zfmisc_1(sK5(sK4,sK3))
    | v1_xboole_0(sK5(sK4,sK3))
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f219,f50])).

fof(f50,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f219,plain,
    ( v1_zfmisc_1(sK5(sK4,sK3))
    | v1_xboole_0(sK5(sK4,sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f214,f188])).

fof(f188,plain,(
    v2_tex_2(sK5(sK4,sK3),sK3) ),
    inference(resolution,[],[f174,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v2_tex_2(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
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

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( X1 = X2
          | ~ r1_tarski(X1,X2)
          | ~ v2_tex_2(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f174,plain,(
    ~ sP0(sK4,sK3) ),
    inference(subsumption_resolution,[],[f166,f156])).

% (19606)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f156,plain,(
    ~ sP1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f155,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( sP0(X1,X0)
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f155,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ sP1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f154,f125])).

fof(f125,plain,(
    sP2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f112,f50])).

fof(f112,plain,
    ( sP2(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f52,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f29,f28,f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ( v3_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f154,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ sP1(sK3,sK4)
    | ~ sP2(sK4,sK3) ),
    inference(resolution,[],[f138,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X0,X1)
      | ~ sP1(X1,X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v3_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f138,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(resolution,[],[f119,f54])).

fof(f54,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f119,plain,
    ( v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f118,f47])).

fof(f118,plain,
    ( v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f117,f48])).

fof(f117,plain,
    ( v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f116,f49])).

fof(f116,plain,
    ( v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f115,plain,
    ( v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f110,f51])).

fof(f51,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f110,plain,
    ( v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3)
    | v1_xboole_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f52,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f166,plain,
    ( sP1(sK3,sK4)
    | ~ sP0(sK4,sK3) ),
    inference(resolution,[],[f163,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ sP0(X1,X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f163,plain,(
    v2_tex_2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f145,f159])).

fof(f159,plain,(
    ~ v3_tex_2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f158,f125])).

fof(f158,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ sP2(sK4,sK3) ),
    inference(resolution,[],[f156,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ v3_tex_2(X0,X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f145,plain,
    ( v2_tex_2(sK4,sK3)
    | v3_tex_2(sK4,sK3) ),
    inference(resolution,[],[f124,f53])).

fof(f53,plain,
    ( v1_zfmisc_1(sK4)
    | v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f124,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f123,f47])).

fof(f123,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f122,f48])).

fof(f122,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f121,f49])).

fof(f121,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f120,f50])).

fof(f120,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f111,f51])).

fof(f111,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4)
    | v1_xboole_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f52,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f214,plain,
    ( v1_zfmisc_1(sK5(sK4,sK3))
    | ~ v2_tex_2(sK5(sK4,sK3),sK3)
    | v1_xboole_0(sK5(sK4,sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f187,f69])).

fof(f187,plain,(
    m1_subset_1(sK5(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f174,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f271,plain,
    ( ~ v1_zfmisc_1(sK5(sK4,sK3))
    | v1_xboole_0(sK5(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f203,f190])).

fof(f190,plain,(
    sK4 != sK5(sK4,sK3) ),
    inference(resolution,[],[f174,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | sK5(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f203,plain,
    ( sK4 = sK5(sK4,sK3)
    | ~ v1_zfmisc_1(sK5(sK4,sK3))
    | v1_xboole_0(sK5(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f202,f51])).

fof(f202,plain,
    ( sK4 = sK5(sK4,sK3)
    | ~ v1_zfmisc_1(sK5(sK4,sK3))
    | v1_xboole_0(sK5(sK4,sK3))
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f189,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f189,plain,(
    r1_tarski(sK4,sK5(sK4,sK3)) ),
    inference(resolution,[],[f174,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r1_tarski(X0,sK5(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f269,plain,(
    k1_xboole_0 != k6_subset_1(sK5(sK4,sK3),sK4) ),
    inference(subsumption_resolution,[],[f200,f190])).

fof(f200,plain,
    ( k1_xboole_0 != k6_subset_1(sK5(sK4,sK3),sK4)
    | sK4 = sK5(sK4,sK3) ),
    inference(resolution,[],[f189,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k6_subset_1(X1,X0)
        & X0 != X1
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:26:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (1209401344)
% 0.14/0.37  ipcrm: permission denied for id (1212678145)
% 0.14/0.37  ipcrm: permission denied for id (1209434114)
% 0.14/0.37  ipcrm: permission denied for id (1209466883)
% 0.14/0.37  ipcrm: permission denied for id (1217134596)
% 0.14/0.37  ipcrm: permission denied for id (1209532422)
% 0.14/0.38  ipcrm: permission denied for id (1209565191)
% 0.14/0.38  ipcrm: permission denied for id (1215299592)
% 0.14/0.38  ipcrm: permission denied for id (1215365130)
% 0.14/0.38  ipcrm: permission denied for id (1209663499)
% 0.14/0.38  ipcrm: permission denied for id (1215430669)
% 0.14/0.38  ipcrm: permission denied for id (1212973070)
% 0.14/0.38  ipcrm: permission denied for id (1209761807)
% 0.14/0.39  ipcrm: permission denied for id (1213005840)
% 0.14/0.39  ipcrm: permission denied for id (1215463441)
% 0.14/0.39  ipcrm: permission denied for id (1209892882)
% 0.14/0.39  ipcrm: permission denied for id (1209925651)
% 0.14/0.39  ipcrm: permission denied for id (1213071380)
% 0.14/0.39  ipcrm: permission denied for id (1215496213)
% 0.14/0.39  ipcrm: permission denied for id (1216675862)
% 0.14/0.39  ipcrm: permission denied for id (1215561751)
% 0.14/0.40  ipcrm: permission denied for id (1213202456)
% 0.14/0.40  ipcrm: permission denied for id (1213235225)
% 0.14/0.40  ipcrm: permission denied for id (1216708634)
% 0.14/0.40  ipcrm: permission denied for id (1217265691)
% 0.14/0.40  ipcrm: permission denied for id (1210089500)
% 0.14/0.40  ipcrm: permission denied for id (1216774173)
% 0.14/0.40  ipcrm: permission denied for id (1213366302)
% 0.14/0.40  ipcrm: permission denied for id (1213399071)
% 0.14/0.40  ipcrm: permission denied for id (1210155040)
% 0.14/0.41  ipcrm: permission denied for id (1216806945)
% 0.20/0.41  ipcrm: permission denied for id (1213464610)
% 0.20/0.41  ipcrm: permission denied for id (1210220579)
% 0.20/0.41  ipcrm: permission denied for id (1210253348)
% 0.20/0.41  ipcrm: permission denied for id (1215725605)
% 0.20/0.41  ipcrm: permission denied for id (1210286118)
% 0.20/0.41  ipcrm: permission denied for id (1213530151)
% 0.20/0.41  ipcrm: permission denied for id (1213562920)
% 0.20/0.41  ipcrm: permission denied for id (1213595689)
% 0.20/0.42  ipcrm: permission denied for id (1213628458)
% 0.20/0.42  ipcrm: permission denied for id (1210417195)
% 0.20/0.42  ipcrm: permission denied for id (1213661228)
% 0.20/0.42  ipcrm: permission denied for id (1215758381)
% 0.20/0.42  ipcrm: permission denied for id (1210515502)
% 0.20/0.42  ipcrm: permission denied for id (1210548271)
% 0.20/0.42  ipcrm: permission denied for id (1216839728)
% 0.20/0.42  ipcrm: permission denied for id (1217298481)
% 0.20/0.43  ipcrm: permission denied for id (1213792306)
% 0.20/0.43  ipcrm: permission denied for id (1210679347)
% 0.20/0.43  ipcrm: permission denied for id (1213825076)
% 0.20/0.43  ipcrm: permission denied for id (1210744885)
% 0.20/0.43  ipcrm: permission denied for id (1210777654)
% 0.20/0.43  ipcrm: permission denied for id (1210810423)
% 0.20/0.43  ipcrm: permission denied for id (1210843192)
% 0.20/0.43  ipcrm: permission denied for id (1213857849)
% 0.20/0.43  ipcrm: permission denied for id (1215856698)
% 0.20/0.44  ipcrm: permission denied for id (1215922235)
% 0.20/0.44  ipcrm: permission denied for id (1215987773)
% 0.20/0.44  ipcrm: permission denied for id (1216938046)
% 0.20/0.44  ipcrm: permission denied for id (1211072575)
% 0.20/0.44  ipcrm: permission denied for id (1214087232)
% 0.20/0.44  ipcrm: permission denied for id (1211138113)
% 0.20/0.44  ipcrm: permission denied for id (1211170882)
% 0.20/0.45  ipcrm: permission denied for id (1216086083)
% 0.20/0.45  ipcrm: permission denied for id (1211269188)
% 0.20/0.45  ipcrm: permission denied for id (1214185541)
% 0.20/0.45  ipcrm: permission denied for id (1211301958)
% 0.20/0.45  ipcrm: permission denied for id (1211334727)
% 0.20/0.45  ipcrm: permission denied for id (1211367496)
% 0.20/0.45  ipcrm: permission denied for id (1214218313)
% 0.20/0.45  ipcrm: permission denied for id (1214251082)
% 0.20/0.46  ipcrm: permission denied for id (1211465803)
% 0.20/0.46  ipcrm: permission denied for id (1211498572)
% 0.20/0.46  ipcrm: permission denied for id (1211531341)
% 0.20/0.46  ipcrm: permission denied for id (1211564110)
% 0.20/0.46  ipcrm: permission denied for id (1211596879)
% 0.20/0.46  ipcrm: permission denied for id (1211629648)
% 0.20/0.46  ipcrm: permission denied for id (1211662417)
% 0.20/0.46  ipcrm: permission denied for id (1214283858)
% 0.20/0.46  ipcrm: permission denied for id (1211695187)
% 0.20/0.47  ipcrm: permission denied for id (1211727956)
% 0.20/0.47  ipcrm: permission denied for id (1217364053)
% 0.20/0.47  ipcrm: permission denied for id (1211760726)
% 0.20/0.47  ipcrm: permission denied for id (1216151639)
% 0.20/0.47  ipcrm: permission denied for id (1211826264)
% 0.20/0.47  ipcrm: permission denied for id (1214382169)
% 0.20/0.47  ipcrm: permission denied for id (1211859034)
% 0.20/0.47  ipcrm: permission denied for id (1214414939)
% 0.20/0.48  ipcrm: permission denied for id (1211891804)
% 0.20/0.48  ipcrm: permission denied for id (1217003613)
% 0.20/0.48  ipcrm: permission denied for id (1211957342)
% 0.20/0.48  ipcrm: permission denied for id (1214513248)
% 0.20/0.48  ipcrm: permission denied for id (1214546017)
% 0.20/0.48  ipcrm: permission denied for id (1216249954)
% 0.20/0.48  ipcrm: permission denied for id (1216282723)
% 0.20/0.49  ipcrm: permission denied for id (1216315492)
% 0.20/0.49  ipcrm: permission denied for id (1214677093)
% 0.20/0.49  ipcrm: permission denied for id (1214709862)
% 0.20/0.49  ipcrm: permission denied for id (1216381031)
% 0.20/0.49  ipcrm: permission denied for id (1214775400)
% 0.20/0.49  ipcrm: permission denied for id (1214808169)
% 0.20/0.49  ipcrm: permission denied for id (1212088426)
% 0.20/0.49  ipcrm: permission denied for id (1212121195)
% 0.20/0.49  ipcrm: permission denied for id (1212153964)
% 0.20/0.50  ipcrm: permission denied for id (1214840941)
% 0.20/0.50  ipcrm: permission denied for id (1214873710)
% 0.20/0.50  ipcrm: permission denied for id (1212219503)
% 0.20/0.50  ipcrm: permission denied for id (1215004785)
% 0.20/0.50  ipcrm: permission denied for id (1212317810)
% 0.20/0.50  ipcrm: permission denied for id (1212350579)
% 0.20/0.50  ipcrm: permission denied for id (1216446580)
% 0.20/0.51  ipcrm: permission denied for id (1215037557)
% 0.20/0.51  ipcrm: permission denied for id (1212416118)
% 0.20/0.51  ipcrm: permission denied for id (1212448887)
% 0.20/0.51  ipcrm: permission denied for id (1215070328)
% 0.20/0.51  ipcrm: permission denied for id (1217101945)
% 0.20/0.51  ipcrm: permission denied for id (1212514426)
% 0.20/0.51  ipcrm: permission denied for id (1212547195)
% 0.20/0.51  ipcrm: permission denied for id (1216512124)
% 0.20/0.51  ipcrm: permission denied for id (1215168637)
% 0.20/0.52  ipcrm: permission denied for id (1212612734)
% 0.20/0.52  ipcrm: permission denied for id (1215201407)
% 0.93/0.63  % (19592)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.93/0.63  % (19600)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.93/0.65  % (19592)Refutation not found, incomplete strategy% (19592)------------------------------
% 0.93/0.65  % (19592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.93/0.65  % (19592)Termination reason: Refutation not found, incomplete strategy
% 0.93/0.65  
% 0.93/0.65  % (19592)Memory used [KB]: 10618
% 0.93/0.65  % (19592)Time elapsed: 0.070 s
% 0.93/0.65  % (19592)------------------------------
% 0.93/0.65  % (19592)------------------------------
% 1.18/0.66  % (19615)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.18/0.66  % (19596)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.18/0.67  % (19591)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.18/0.67  % (19597)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.18/0.67  % (19612)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.18/0.67  % (19591)Refutation not found, incomplete strategy% (19591)------------------------------
% 1.18/0.67  % (19591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.67  % (19591)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.67  
% 1.18/0.67  % (19591)Memory used [KB]: 10618
% 1.18/0.67  % (19591)Time elapsed: 0.093 s
% 1.18/0.67  % (19591)------------------------------
% 1.18/0.67  % (19591)------------------------------
% 1.18/0.67  % (19597)Refutation not found, incomplete strategy% (19597)------------------------------
% 1.18/0.67  % (19597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.67  % (19597)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.67  
% 1.18/0.67  % (19597)Memory used [KB]: 10618
% 1.18/0.67  % (19597)Time elapsed: 0.093 s
% 1.18/0.67  % (19597)------------------------------
% 1.18/0.67  % (19597)------------------------------
% 1.18/0.67  % (19599)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.18/0.67  % (19594)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.18/0.67  % (19599)Refutation found. Thanks to Tanya!
% 1.18/0.67  % SZS status Theorem for theBenchmark
% 1.18/0.67  % SZS output start Proof for theBenchmark
% 1.18/0.67  fof(f281,plain,(
% 1.18/0.67    $false),
% 1.18/0.67    inference(trivial_inequality_removal,[],[f277])).
% 1.18/0.67  fof(f277,plain,(
% 1.18/0.67    k1_xboole_0 != k1_xboole_0),
% 1.18/0.67    inference(superposition,[],[f269,f276])).
% 1.18/0.67  fof(f276,plain,(
% 1.18/0.67    ( ! [X0] : (k1_xboole_0 = k6_subset_1(sK5(sK4,sK3),X0)) )),
% 1.18/0.67    inference(resolution,[],[f275,f72])).
% 1.18/0.67  fof(f72,plain,(
% 1.18/0.67    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.18/0.67    inference(cnf_transformation,[],[f2])).
% 1.18/0.67  fof(f2,axiom,(
% 1.18/0.67    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.18/0.67  fof(f275,plain,(
% 1.18/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK5(sK4,sK3))) | k1_xboole_0 = X0) )),
% 1.18/0.67    inference(resolution,[],[f273,f71])).
% 1.18/0.67  fof(f71,plain,(
% 1.18/0.67    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 1.18/0.67    inference(cnf_transformation,[],[f46])).
% 1.18/0.67  fof(f46,plain,(
% 1.18/0.67    ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0)),
% 1.18/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f45])).
% 1.18/0.67  fof(f45,plain,(
% 1.18/0.67    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.18/0.67    introduced(choice_axiom,[])).
% 1.18/0.67  fof(f24,plain,(
% 1.18/0.67    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.18/0.67    inference(ennf_transformation,[],[f12])).
% 1.18/0.67  fof(f12,plain,(
% 1.18/0.67    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.18/0.67    inference(pure_predicate_removal,[],[f4])).
% 1.18/0.67  fof(f4,axiom,(
% 1.18/0.67    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 1.18/0.67  fof(f273,plain,(
% 1.18/0.67    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK5(sK4,sK3)))) )),
% 1.18/0.67    inference(resolution,[],[f272,f74])).
% 1.18/0.67  fof(f74,plain,(
% 1.18/0.67    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.18/0.67    inference(cnf_transformation,[],[f26])).
% 1.18/0.67  fof(f26,plain,(
% 1.18/0.67    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.18/0.67    inference(ennf_transformation,[],[f3])).
% 1.18/0.67  fof(f3,axiom,(
% 1.18/0.67    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.18/0.67  fof(f272,plain,(
% 1.18/0.67    v1_xboole_0(sK5(sK4,sK3))),
% 1.18/0.67    inference(subsumption_resolution,[],[f271,f224])).
% 1.18/0.67  fof(f224,plain,(
% 1.18/0.67    v1_zfmisc_1(sK5(sK4,sK3))),
% 1.18/0.67    inference(subsumption_resolution,[],[f223,f68])).
% 1.18/0.67  fof(f68,plain,(
% 1.18/0.67    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 1.18/0.67    inference(cnf_transformation,[],[f21])).
% 1.18/0.67  fof(f21,plain,(
% 1.18/0.67    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.18/0.67    inference(ennf_transformation,[],[f1])).
% 1.18/0.67  fof(f1,axiom,(
% 1.18/0.67    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 1.18/0.67  fof(f223,plain,(
% 1.18/0.67    v1_zfmisc_1(sK5(sK4,sK3)) | v1_xboole_0(sK5(sK4,sK3))),
% 1.18/0.67    inference(subsumption_resolution,[],[f222,f47])).
% 1.18/0.67  fof(f47,plain,(
% 1.18/0.67    ~v2_struct_0(sK3)),
% 1.18/0.67    inference(cnf_transformation,[],[f35])).
% 1.18/0.67  fof(f35,plain,(
% 1.18/0.67    ((~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 1.18/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f34,f33])).
% 1.18/0.67  fof(f33,plain,(
% 1.18/0.67    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.18/0.67    introduced(choice_axiom,[])).
% 1.18/0.67  fof(f34,plain,(
% 1.18/0.67    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4))),
% 1.18/0.67    introduced(choice_axiom,[])).
% 1.18/0.67  fof(f32,plain,(
% 1.18/0.67    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.18/0.67    inference(flattening,[],[f31])).
% 1.18/0.67  fof(f31,plain,(
% 1.18/0.67    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.18/0.67    inference(nnf_transformation,[],[f14])).
% 1.18/0.67  fof(f14,plain,(
% 1.18/0.67    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.18/0.67    inference(flattening,[],[f13])).
% 1.18/0.67  fof(f13,plain,(
% 1.18/0.67    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.18/0.67    inference(ennf_transformation,[],[f11])).
% 1.18/0.67  fof(f11,negated_conjecture,(
% 1.18/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.18/0.67    inference(negated_conjecture,[],[f10])).
% 1.18/0.67  fof(f10,conjecture,(
% 1.18/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).
% 1.18/0.67  fof(f222,plain,(
% 1.18/0.67    v1_zfmisc_1(sK5(sK4,sK3)) | v1_xboole_0(sK5(sK4,sK3)) | v2_struct_0(sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f221,f48])).
% 1.18/0.67  fof(f48,plain,(
% 1.18/0.67    v2_pre_topc(sK3)),
% 1.18/0.67    inference(cnf_transformation,[],[f35])).
% 1.18/0.67  fof(f221,plain,(
% 1.18/0.67    v1_zfmisc_1(sK5(sK4,sK3)) | v1_xboole_0(sK5(sK4,sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f220,f49])).
% 1.18/0.67  fof(f49,plain,(
% 1.18/0.67    v2_tdlat_3(sK3)),
% 1.18/0.67    inference(cnf_transformation,[],[f35])).
% 1.18/0.67  fof(f220,plain,(
% 1.18/0.67    v1_zfmisc_1(sK5(sK4,sK3)) | v1_xboole_0(sK5(sK4,sK3)) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f219,f50])).
% 1.18/0.67  fof(f50,plain,(
% 1.18/0.67    l1_pre_topc(sK3)),
% 1.18/0.67    inference(cnf_transformation,[],[f35])).
% 1.18/0.67  fof(f219,plain,(
% 1.18/0.67    v1_zfmisc_1(sK5(sK4,sK3)) | v1_xboole_0(sK5(sK4,sK3)) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f214,f188])).
% 1.18/0.67  fof(f188,plain,(
% 1.18/0.67    v2_tex_2(sK5(sK4,sK3),sK3)),
% 1.18/0.67    inference(resolution,[],[f174,f64])).
% 1.18/0.67  fof(f64,plain,(
% 1.18/0.67    ( ! [X0,X1] : (sP0(X0,X1) | v2_tex_2(sK5(X0,X1),X1)) )),
% 1.18/0.67    inference(cnf_transformation,[],[f43])).
% 1.18/0.67  fof(f43,plain,(
% 1.18/0.67    ! [X0,X1] : ((sP0(X0,X1) | (sK5(X0,X1) != X0 & r1_tarski(X0,sK5(X0,X1)) & v2_tex_2(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.18/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 1.18/0.67  fof(f42,plain,(
% 1.18/0.67    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK5(X0,X1) != X0 & r1_tarski(X0,sK5(X0,X1)) & v2_tex_2(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.18/0.67    introduced(choice_axiom,[])).
% 1.18/0.67  fof(f41,plain,(
% 1.18/0.67    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.18/0.67    inference(rectify,[],[f40])).
% 1.18/0.67  fof(f40,plain,(
% 1.18/0.67    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 1.18/0.67    inference(nnf_transformation,[],[f27])).
% 1.18/0.67  fof(f27,plain,(
% 1.18/0.67    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.18/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.18/0.67  fof(f174,plain,(
% 1.18/0.67    ~sP0(sK4,sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f166,f156])).
% 1.18/0.67  % (19606)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.18/0.67  fof(f156,plain,(
% 1.18/0.67    ~sP1(sK3,sK4)),
% 1.18/0.67    inference(subsumption_resolution,[],[f155,f59])).
% 1.18/0.67  fof(f59,plain,(
% 1.18/0.67    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~sP1(X0,X1)) )),
% 1.18/0.67    inference(cnf_transformation,[],[f39])).
% 1.18/0.67  fof(f39,plain,(
% 1.18/0.67    ! [X0,X1] : ((sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 1.18/0.67    inference(flattening,[],[f38])).
% 1.18/0.67  fof(f38,plain,(
% 1.18/0.67    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(X1,X0) | ~v2_tex_2(X1,X0))) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 1.18/0.67    inference(nnf_transformation,[],[f28])).
% 1.18/0.67  fof(f28,plain,(
% 1.18/0.67    ! [X0,X1] : (sP1(X0,X1) <=> (sP0(X1,X0) & v2_tex_2(X1,X0)))),
% 1.18/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.18/0.67  fof(f155,plain,(
% 1.18/0.67    ~v2_tex_2(sK4,sK3) | ~sP1(sK3,sK4)),
% 1.18/0.67    inference(subsumption_resolution,[],[f154,f125])).
% 1.18/0.67  fof(f125,plain,(
% 1.18/0.67    sP2(sK4,sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f112,f50])).
% 1.18/0.67  fof(f112,plain,(
% 1.18/0.67    sP2(sK4,sK3) | ~l1_pre_topc(sK3)),
% 1.18/0.67    inference(resolution,[],[f52,f67])).
% 1.18/0.67  fof(f67,plain,(
% 1.18/0.67    ( ! [X0,X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.18/0.67    inference(cnf_transformation,[],[f30])).
% 1.18/0.67  fof(f30,plain,(
% 1.18/0.67    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.18/0.67    inference(definition_folding,[],[f20,f29,f28,f27])).
% 1.18/0.67  fof(f29,plain,(
% 1.18/0.67    ! [X1,X0] : ((v3_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 1.18/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.18/0.67  fof(f20,plain,(
% 1.18/0.67    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.18/0.67    inference(flattening,[],[f19])).
% 1.18/0.67  fof(f19,plain,(
% 1.18/0.67    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.18/0.67    inference(ennf_transformation,[],[f6])).
% 1.18/0.67  fof(f6,axiom,(
% 1.18/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 1.18/0.67  fof(f52,plain,(
% 1.18/0.67    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.18/0.67    inference(cnf_transformation,[],[f35])).
% 1.18/0.67  fof(f154,plain,(
% 1.18/0.67    ~v2_tex_2(sK4,sK3) | ~sP1(sK3,sK4) | ~sP2(sK4,sK3)),
% 1.18/0.67    inference(resolution,[],[f138,f58])).
% 1.18/0.67  fof(f58,plain,(
% 1.18/0.67    ( ! [X0,X1] : (v3_tex_2(X0,X1) | ~sP1(X1,X0) | ~sP2(X0,X1)) )),
% 1.18/0.67    inference(cnf_transformation,[],[f37])).
% 1.18/0.67  fof(f37,plain,(
% 1.18/0.67    ! [X0,X1] : (((v3_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v3_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 1.18/0.67    inference(rectify,[],[f36])).
% 1.18/0.67  fof(f36,plain,(
% 1.18/0.67    ! [X1,X0] : (((v3_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v3_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 1.18/0.67    inference(nnf_transformation,[],[f29])).
% 1.18/0.67  fof(f138,plain,(
% 1.18/0.67    ~v3_tex_2(sK4,sK3) | ~v2_tex_2(sK4,sK3)),
% 1.18/0.67    inference(resolution,[],[f119,f54])).
% 1.18/0.67  fof(f54,plain,(
% 1.18/0.67    ~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)),
% 1.18/0.67    inference(cnf_transformation,[],[f35])).
% 1.18/0.67  fof(f119,plain,(
% 1.18/0.67    v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f118,f47])).
% 1.18/0.67  fof(f118,plain,(
% 1.18/0.67    v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3) | v2_struct_0(sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f117,f48])).
% 1.18/0.67  fof(f117,plain,(
% 1.18/0.67    v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f116,f49])).
% 1.18/0.67  fof(f116,plain,(
% 1.18/0.67    v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f115,f50])).
% 1.18/0.67  fof(f115,plain,(
% 1.18/0.67    v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f110,f51])).
% 1.18/0.67  fof(f51,plain,(
% 1.18/0.67    ~v1_xboole_0(sK4)),
% 1.18/0.67    inference(cnf_transformation,[],[f35])).
% 1.18/0.67  fof(f110,plain,(
% 1.18/0.67    v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3) | v1_xboole_0(sK4) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.18/0.67    inference(resolution,[],[f52,f69])).
% 1.18/0.67  fof(f69,plain,(
% 1.18/0.67    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.18/0.67    inference(cnf_transformation,[],[f44])).
% 1.18/0.67  fof(f44,plain,(
% 1.18/0.67    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.18/0.67    inference(nnf_transformation,[],[f23])).
% 1.18/0.67  fof(f23,plain,(
% 1.18/0.67    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.18/0.67    inference(flattening,[],[f22])).
% 1.18/0.67  fof(f22,plain,(
% 1.18/0.67    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.18/0.67    inference(ennf_transformation,[],[f9])).
% 1.18/0.67  fof(f9,axiom,(
% 1.18/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 1.18/0.67  fof(f166,plain,(
% 1.18/0.67    sP1(sK3,sK4) | ~sP0(sK4,sK3)),
% 1.18/0.67    inference(resolution,[],[f163,f61])).
% 1.18/0.67  fof(f61,plain,(
% 1.18/0.67    ( ! [X0,X1] : (sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) )),
% 1.18/0.67    inference(cnf_transformation,[],[f39])).
% 1.18/0.67  fof(f163,plain,(
% 1.18/0.67    v2_tex_2(sK4,sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f145,f159])).
% 1.18/0.67  fof(f159,plain,(
% 1.18/0.67    ~v3_tex_2(sK4,sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f158,f125])).
% 1.18/0.67  fof(f158,plain,(
% 1.18/0.67    ~v3_tex_2(sK4,sK3) | ~sP2(sK4,sK3)),
% 1.18/0.67    inference(resolution,[],[f156,f57])).
% 1.18/0.67  fof(f57,plain,(
% 1.18/0.67    ( ! [X0,X1] : (sP1(X1,X0) | ~v3_tex_2(X0,X1) | ~sP2(X0,X1)) )),
% 1.18/0.67    inference(cnf_transformation,[],[f37])).
% 1.18/0.67  fof(f145,plain,(
% 1.18/0.67    v2_tex_2(sK4,sK3) | v3_tex_2(sK4,sK3)),
% 1.18/0.67    inference(resolution,[],[f124,f53])).
% 1.18/0.67  fof(f53,plain,(
% 1.18/0.67    v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)),
% 1.18/0.67    inference(cnf_transformation,[],[f35])).
% 1.18/0.67  fof(f124,plain,(
% 1.18/0.67    ~v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f123,f47])).
% 1.18/0.67  fof(f123,plain,(
% 1.18/0.67    v2_tex_2(sK4,sK3) | ~v1_zfmisc_1(sK4) | v2_struct_0(sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f122,f48])).
% 1.18/0.67  fof(f122,plain,(
% 1.18/0.67    v2_tex_2(sK4,sK3) | ~v1_zfmisc_1(sK4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f121,f49])).
% 1.18/0.67  fof(f121,plain,(
% 1.18/0.67    v2_tex_2(sK4,sK3) | ~v1_zfmisc_1(sK4) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f120,f50])).
% 1.18/0.67  fof(f120,plain,(
% 1.18/0.67    v2_tex_2(sK4,sK3) | ~v1_zfmisc_1(sK4) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.18/0.67    inference(subsumption_resolution,[],[f111,f51])).
% 1.18/0.67  fof(f111,plain,(
% 1.18/0.67    v2_tex_2(sK4,sK3) | ~v1_zfmisc_1(sK4) | v1_xboole_0(sK4) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.18/0.67    inference(resolution,[],[f52,f70])).
% 1.18/0.67  fof(f70,plain,(
% 1.18/0.67    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.18/0.67    inference(cnf_transformation,[],[f44])).
% 1.18/0.67  fof(f214,plain,(
% 1.18/0.67    v1_zfmisc_1(sK5(sK4,sK3)) | ~v2_tex_2(sK5(sK4,sK3),sK3) | v1_xboole_0(sK5(sK4,sK3)) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.18/0.67    inference(resolution,[],[f187,f69])).
% 1.18/0.67  fof(f187,plain,(
% 1.18/0.67    m1_subset_1(sK5(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.18/0.67    inference(resolution,[],[f174,f63])).
% 1.18/0.67  fof(f63,plain,(
% 1.18/0.67    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.18/0.67    inference(cnf_transformation,[],[f43])).
% 1.18/0.67  fof(f271,plain,(
% 1.18/0.67    ~v1_zfmisc_1(sK5(sK4,sK3)) | v1_xboole_0(sK5(sK4,sK3))),
% 1.18/0.67    inference(subsumption_resolution,[],[f203,f190])).
% 1.18/0.67  fof(f190,plain,(
% 1.18/0.67    sK4 != sK5(sK4,sK3)),
% 1.18/0.67    inference(resolution,[],[f174,f66])).
% 1.18/0.67  fof(f66,plain,(
% 1.18/0.67    ( ! [X0,X1] : (sP0(X0,X1) | sK5(X0,X1) != X0) )),
% 1.18/0.67    inference(cnf_transformation,[],[f43])).
% 1.18/0.67  fof(f203,plain,(
% 1.18/0.67    sK4 = sK5(sK4,sK3) | ~v1_zfmisc_1(sK5(sK4,sK3)) | v1_xboole_0(sK5(sK4,sK3))),
% 1.18/0.67    inference(subsumption_resolution,[],[f202,f51])).
% 1.18/0.67  fof(f202,plain,(
% 1.18/0.67    sK4 = sK5(sK4,sK3) | ~v1_zfmisc_1(sK5(sK4,sK3)) | v1_xboole_0(sK5(sK4,sK3)) | v1_xboole_0(sK4)),
% 1.18/0.67    inference(resolution,[],[f189,f55])).
% 1.18/0.67  fof(f55,plain,(
% 1.18/0.67    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.18/0.67    inference(cnf_transformation,[],[f16])).
% 1.18/0.67  fof(f16,plain,(
% 1.18/0.67    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.18/0.67    inference(flattening,[],[f15])).
% 1.18/0.67  fof(f15,plain,(
% 1.18/0.67    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.18/0.67    inference(ennf_transformation,[],[f8])).
% 1.18/0.67  fof(f8,axiom,(
% 1.18/0.67    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.18/0.67  fof(f189,plain,(
% 1.18/0.67    r1_tarski(sK4,sK5(sK4,sK3))),
% 1.18/0.67    inference(resolution,[],[f174,f65])).
% 1.18/0.67  fof(f65,plain,(
% 1.18/0.67    ( ! [X0,X1] : (sP0(X0,X1) | r1_tarski(X0,sK5(X0,X1))) )),
% 1.18/0.67    inference(cnf_transformation,[],[f43])).
% 1.18/0.67  fof(f269,plain,(
% 1.18/0.67    k1_xboole_0 != k6_subset_1(sK5(sK4,sK3),sK4)),
% 1.18/0.67    inference(subsumption_resolution,[],[f200,f190])).
% 1.18/0.67  fof(f200,plain,(
% 1.18/0.67    k1_xboole_0 != k6_subset_1(sK5(sK4,sK3),sK4) | sK4 = sK5(sK4,sK3)),
% 1.18/0.67    inference(resolution,[],[f189,f73])).
% 1.18/0.67  fof(f73,plain,(
% 1.18/0.67    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.18/0.67    inference(cnf_transformation,[],[f25])).
% 1.18/0.67  fof(f25,plain,(
% 1.18/0.67    ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1))),
% 1.18/0.67    inference(ennf_transformation,[],[f7])).
% 1.18/0.67  fof(f7,axiom,(
% 1.18/0.67    ! [X0,X1] : ~(k1_xboole_0 = k6_subset_1(X1,X0) & X0 != X1 & r1_tarski(X0,X1))),
% 1.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_tex_2)).
% 1.18/0.67  % SZS output end Proof for theBenchmark
% 1.18/0.67  % (19599)------------------------------
% 1.18/0.67  % (19599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.67  % (19599)Termination reason: Refutation
% 1.18/0.67  
% 1.18/0.67  % (19599)Memory used [KB]: 1663
% 1.18/0.67  % (19599)Time elapsed: 0.096 s
% 1.18/0.67  % (19599)------------------------------
% 1.18/0.67  % (19599)------------------------------
% 1.18/0.68  % (19420)Success in time 0.315 s
%------------------------------------------------------------------------------
