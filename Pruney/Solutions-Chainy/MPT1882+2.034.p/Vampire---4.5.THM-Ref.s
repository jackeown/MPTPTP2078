%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 (3031 expanded)
%              Number of leaves         :   15 ( 845 expanded)
%              Depth                    :   28
%              Number of atoms          :  457 (25577 expanded)
%              Number of equality atoms :   45 ( 435 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(global_subsumption,[],[f244,f249])).

% (24827)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f249,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f243,f81])).

fof(f81,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f68,f75])).

fof(f75,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f69,f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
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

fof(f243,plain,(
    r1_tarski(sK3,k1_xboole_0) ),
    inference(global_subsumption,[],[f158,f185,f235])).

fof(f235,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(superposition,[],[f61,f222])).

fof(f222,plain,(
    k1_xboole_0 = sK4(sK3,sK2) ),
    inference(global_subsumption,[],[f158,f185,f219])).

fof(f219,plain,
    ( sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | k1_xboole_0 = sK4(sK3,sK2) ),
    inference(trivial_inequality_removal,[],[f212])).

fof(f212,plain,
    ( sK3 != sK3
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | k1_xboole_0 = sK4(sK3,sK2) ),
    inference(superposition,[],[f62,f199])).

fof(f199,plain,
    ( sK3 = sK4(sK3,sK2)
    | k1_xboole_0 = sK4(sK3,sK2) ),
    inference(resolution,[],[f198,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f71,f51])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f198,plain,
    ( v1_xboole_0(sK4(sK3,sK2))
    | sK3 = sK4(sK3,sK2) ),
    inference(global_subsumption,[],[f47,f158,f185,f194])).

fof(f194,plain,
    ( v1_xboole_0(sK4(sK3,sK2))
    | sK3 = sK4(sK3,sK2)
    | v1_xboole_0(sK3)
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(resolution,[],[f188,f61])).

fof(f188,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK4(sK3,sK2))
      | v1_xboole_0(sK4(sK3,sK2))
      | sK4(sK3,sK2) = X0
      | v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f158,f187])).

fof(f187,plain,(
    ! [X0] :
      ( sP0(sK3,sK2)
      | v1_xboole_0(sK4(sK3,sK2))
      | ~ r1_tarski(X0,sK4(sK3,sK2))
      | sK4(sK3,sK2) = X0
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f185,f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X0,sK2)
      | sP0(X0,sK2)
      | v1_xboole_0(sK4(X0,sK2))
      | ~ r1_tarski(X1,sK4(X0,sK2))
      | sK4(X0,sK2) = X1
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(sK4(X0,sK2))
      | sP0(X0,sK2)
      | ~ v2_tex_2(X0,sK2)
      | ~ r1_tarski(X1,sK4(X0,sK2))
      | sK4(X0,sK2) = X1
      | v1_xboole_0(sK4(X0,sK2))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f171,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f171,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK4(X0,sK2))
      | v1_xboole_0(sK4(X0,sK2))
      | sP0(X0,sK2)
      | ~ v2_tex_2(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X0] :
      ( v1_xboole_0(sK4(X0,sK2))
      | v1_zfmisc_1(sK4(X0,sK2))
      | sP0(X0,sK2)
      | ~ v2_tex_2(X0,sK2)
      | sP0(X0,sK2)
      | ~ v2_tex_2(X0,sK2) ) ),
    inference(resolution,[],[f155,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK4(X0,X1),X1)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
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

fof(f155,plain,(
    ! [X1] :
      ( ~ v2_tex_2(sK4(X1,sK2),sK2)
      | v1_xboole_0(sK4(X1,sK2))
      | v1_zfmisc_1(sK4(X1,sK2))
      | sP0(X1,sK2)
      | ~ v2_tex_2(X1,sK2) ) ),
    inference(resolution,[],[f151,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f151,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_tex_2(X0,sK2)
      | v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(global_subsumption,[],[f46,f45,f43,f148])).

fof(f148,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_tdlat_3(sK2)
      | v1_zfmisc_1(X0)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,(
    v2_pre_topc(sK2) ),
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v1_zfmisc_1(X1)
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

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK4(X0,X1))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f185,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(global_subsumption,[],[f46,f45,f43,f183])).

fof(f183,plain,
    ( v2_tex_2(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f182,f48])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f47,f54,f179])).

fof(f179,plain,(
    ! [X0] :
      ( v2_tex_2(sK3,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f65,f156])).

fof(f156,plain,(
    v1_zfmisc_1(sK3) ),
    inference(global_subsumption,[],[f49,f47,f96,f154])).

fof(f154,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | v1_xboole_0(sK3)
    | v1_zfmisc_1(sK3) ),
    inference(resolution,[],[f151,f48])).

fof(f96,plain,
    ( v2_tex_2(sK3,sK2)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(resolution,[],[f92,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,
    ( sP0(sK3,sK2)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(resolution,[],[f87,f55])).

fof(f55,plain,(
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

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f87,plain,(
    sP1(sK2,sK3) ),
    inference(resolution,[],[f85,f48])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f63,f46])).

fof(f63,plain,(
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
    inference(definition_folding,[],[f21,f26,f25])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f8])).

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

fof(f49,plain,
    ( v3_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f54,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f158,plain,(
    ~ sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f91,f157])).

fof(f157,plain,(
    ~ v3_tex_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f50,f156])).

fof(f50,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,
    ( ~ sP0(sK3,sK2)
    | v3_tex_2(sK3,sK2) ),
    inference(resolution,[],[f87,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f244,plain,(
    k1_xboole_0 != sK3 ),
    inference(global_subsumption,[],[f158,f185,f236])).

fof(f236,plain,
    ( k1_xboole_0 != sK3
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(superposition,[],[f62,f222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:34:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.52  % (24834)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (24826)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (24825)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (24824)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (24828)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (24843)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (24833)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (24823)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (24834)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (24844)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (24841)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.55  % (24835)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (24836)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (24832)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.55  % (24839)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.56  % (24842)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f251,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(global_subsumption,[],[f244,f249])).
% 0.21/0.56  % (24827)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.56  fof(f249,plain,(
% 0.21/0.56    k1_xboole_0 = sK3),
% 0.21/0.56    inference(resolution,[],[f243,f81])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.21/0.56    inference(resolution,[],[f68,f75])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(resolution,[],[f69,f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.56    inference(nnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(flattening,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.56  fof(f243,plain,(
% 0.21/0.56    r1_tarski(sK3,k1_xboole_0)),
% 0.21/0.56    inference(global_subsumption,[],[f158,f185,f235])).
% 0.21/0.56  fof(f235,plain,(
% 0.21/0.56    r1_tarski(sK3,k1_xboole_0) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.21/0.56    inference(superposition,[],[f61,f222])).
% 0.21/0.56  fof(f222,plain,(
% 0.21/0.56    k1_xboole_0 = sK4(sK3,sK2)),
% 0.21/0.56    inference(global_subsumption,[],[f158,f185,f219])).
% 0.21/0.56  fof(f219,plain,(
% 0.21/0.56    sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | k1_xboole_0 = sK4(sK3,sK2)),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f212])).
% 0.21/0.56  fof(f212,plain,(
% 0.21/0.56    sK3 != sK3 | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | k1_xboole_0 = sK4(sK3,sK2)),
% 0.21/0.56    inference(superposition,[],[f62,f199])).
% 0.21/0.56  fof(f199,plain,(
% 0.21/0.56    sK3 = sK4(sK3,sK2) | k1_xboole_0 = sK4(sK3,sK2)),
% 0.21/0.56    inference(resolution,[],[f198,f78])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(resolution,[],[f71,f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    v1_xboole_0(k1_xboole_0)),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    v1_xboole_0(k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.56  fof(f198,plain,(
% 0.21/0.56    v1_xboole_0(sK4(sK3,sK2)) | sK3 = sK4(sK3,sK2)),
% 0.21/0.56    inference(global_subsumption,[],[f47,f158,f185,f194])).
% 0.21/0.56  fof(f194,plain,(
% 0.21/0.56    v1_xboole_0(sK4(sK3,sK2)) | sK3 = sK4(sK3,sK2) | v1_xboole_0(sK3) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.21/0.56    inference(resolution,[],[f188,f61])).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(X0,sK4(sK3,sK2)) | v1_xboole_0(sK4(sK3,sK2)) | sK4(sK3,sK2) = X0 | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(global_subsumption,[],[f158,f187])).
% 0.21/0.56  fof(f187,plain,(
% 0.21/0.56    ( ! [X0] : (sP0(sK3,sK2) | v1_xboole_0(sK4(sK3,sK2)) | ~r1_tarski(X0,sK4(sK3,sK2)) | sK4(sK3,sK2) = X0 | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(resolution,[],[f185,f173])).
% 0.21/0.56  fof(f173,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v2_tex_2(X0,sK2) | sP0(X0,sK2) | v1_xboole_0(sK4(X0,sK2)) | ~r1_tarski(X1,sK4(X0,sK2)) | sK4(X0,sK2) = X1 | v1_xboole_0(X1)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f172])).
% 0.21/0.56  fof(f172,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_xboole_0(sK4(X0,sK2)) | sP0(X0,sK2) | ~v2_tex_2(X0,sK2) | ~r1_tarski(X1,sK4(X0,sK2)) | sK4(X0,sK2) = X1 | v1_xboole_0(sK4(X0,sK2)) | v1_xboole_0(X1)) )),
% 0.21/0.56    inference(resolution,[],[f171,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.56    inference(flattening,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.56  fof(f171,plain,(
% 0.21/0.56    ( ! [X0] : (v1_zfmisc_1(sK4(X0,sK2)) | v1_xboole_0(sK4(X0,sK2)) | sP0(X0,sK2) | ~v2_tex_2(X0,sK2)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f170])).
% 0.21/0.56  fof(f170,plain,(
% 0.21/0.56    ( ! [X0] : (v1_xboole_0(sK4(X0,sK2)) | v1_zfmisc_1(sK4(X0,sK2)) | sP0(X0,sK2) | ~v2_tex_2(X0,sK2) | sP0(X0,sK2) | ~v2_tex_2(X0,sK2)) )),
% 0.21/0.56    inference(resolution,[],[f155,f60])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v2_tex_2(sK4(X0,X1),X1) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1] : ((sP0(X0,X1) | (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 0.21/0.56    inference(rectify,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 0.21/0.56    inference(flattening,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 0.21/0.56    inference(nnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.56  fof(f155,plain,(
% 0.21/0.56    ( ! [X1] : (~v2_tex_2(sK4(X1,sK2),sK2) | v1_xboole_0(sK4(X1,sK2)) | v1_zfmisc_1(sK4(X1,sK2)) | sP0(X1,sK2) | ~v2_tex_2(X1,sK2)) )),
% 0.21/0.56    inference(resolution,[],[f151,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f38])).
% 0.21/0.56  fof(f151,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_tex_2(X0,sK2) | v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 0.21/0.56    inference(global_subsumption,[],[f46,f45,f43,f148])).
% 0.21/0.56  fof(f148,plain,(
% 0.21/0.56    ( ! [X0] : (~v2_tex_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X0) | ~l1_pre_topc(sK2) | ~v2_tdlat_3(sK2) | v1_zfmisc_1(X0) | v2_struct_0(sK2)) )),
% 0.21/0.56    inference(resolution,[],[f64,f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    v2_pre_topc(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f31,f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,negated_conjecture,(
% 0.21/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.56    inference(negated_conjecture,[],[f11])).
% 0.21/0.56  fof(f11,conjecture,(
% 0.21/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v1_zfmisc_1(X1) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ~v2_struct_0(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    v2_tdlat_3(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    l1_pre_topc(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ~v1_xboole_0(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sK4(X0,X1) != X0 | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f38])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,sK4(X0,X1)) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f38])).
% 0.21/0.56  fof(f185,plain,(
% 0.21/0.56    v2_tex_2(sK3,sK2)),
% 0.21/0.56    inference(global_subsumption,[],[f46,f45,f43,f183])).
% 0.21/0.56  fof(f183,plain,(
% 0.21/0.56    v2_tex_2(sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_tdlat_3(sK2) | v2_struct_0(sK2)),
% 0.21/0.56    inference(resolution,[],[f182,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f182,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(sK3,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(global_subsumption,[],[f47,f54,f179])).
% 0.21/0.56  fof(f179,plain,(
% 0.21/0.56    ( ! [X0] : (v2_tex_2(sK3,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(sK3) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(resolution,[],[f65,f156])).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    v1_zfmisc_1(sK3)),
% 0.21/0.56    inference(global_subsumption,[],[f49,f47,f96,f154])).
% 0.21/0.56  fof(f154,plain,(
% 0.21/0.56    ~v2_tex_2(sK3,sK2) | v1_xboole_0(sK3) | v1_zfmisc_1(sK3)),
% 0.21/0.56    inference(resolution,[],[f151,f48])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    v2_tex_2(sK3,sK2) | ~v3_tex_2(sK3,sK2)),
% 0.21/0.56    inference(resolution,[],[f92,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~sP0(X0,X1) | v2_tex_2(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f38])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    sP0(sK3,sK2) | ~v3_tex_2(sK3,sK2)),
% 0.21/0.56    inference(resolution,[],[f87,f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~sP1(X0,X1) | ~v3_tex_2(X1,X0) | sP0(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1] : (((v3_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0,X1] : ((v3_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    sP1(sK2,sK3)),
% 0.21/0.56    inference(resolution,[],[f85,f48])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 0.21/0.56    inference(resolution,[],[f63,f46])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(definition_folding,[],[f21,f26,f25])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    v3_tex_2(sK3,sK2) | v1_zfmisc_1(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.21/0.56  fof(f158,plain,(
% 0.21/0.56    ~sP0(sK3,sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f91,f157])).
% 0.21/0.56  fof(f157,plain,(
% 0.21/0.56    ~v3_tex_2(sK3,sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f50,f156])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ~v3_tex_2(sK3,sK2) | ~v1_zfmisc_1(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    ~sP0(sK3,sK2) | v3_tex_2(sK3,sK2)),
% 0.21/0.56    inference(resolution,[],[f87,f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f244,plain,(
% 0.21/0.56    k1_xboole_0 != sK3),
% 0.21/0.56    inference(global_subsumption,[],[f158,f185,f236])).
% 0.21/0.56  fof(f236,plain,(
% 0.21/0.56    k1_xboole_0 != sK3 | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.21/0.56    inference(superposition,[],[f62,f222])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (24834)------------------------------
% 0.21/0.56  % (24834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24834)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (24834)Memory used [KB]: 6396
% 0.21/0.56  % (24834)Time elapsed: 0.126 s
% 0.21/0.56  % (24834)------------------------------
% 0.21/0.56  % (24834)------------------------------
% 0.21/0.56  % (24821)Success in time 0.199 s
%------------------------------------------------------------------------------
