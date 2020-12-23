%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 422 expanded)
%              Number of leaves         :   22 ( 133 expanded)
%              Depth                    :   22
%              Number of atoms          :  400 (2723 expanded)
%              Number of equality atoms :   43 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3292,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3247,f253])).

fof(f253,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(subsumption_resolution,[],[f252,f57])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

% (19704)Refutation not found, incomplete strategy% (19704)------------------------------
% (19704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19704)Termination reason: Refutation not found, incomplete strategy

% (19704)Memory used [KB]: 10746
% (19704)Time elapsed: 0.076 s
% (19704)------------------------------
% (19704)------------------------------
fof(f252,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_subset_1(X0,X0) ) ),
    inference(forward_demodulation,[],[f246,f149])).

fof(f149,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f110,f138])).

fof(f138,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f124,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f66,f75])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f66,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f124,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f83,f58])).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f76,f77,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f110,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f78,f95])).

fof(f95,plain,(
    ! [X2] : m1_subset_1(X2,k1_zfmisc_1(X2)) ),
    inference(resolution,[],[f82,f84])).

fof(f84,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f75,f58])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f246,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X0))
      | ~ v1_subset_1(X0,X0) ) ),
    inference(resolution,[],[f245,f95])).

fof(f245,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f80,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & v1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

fof(f3247,plain,(
    v1_subset_1(sK3,sK3) ),
    inference(backward_demodulation,[],[f56,f3245])).

fof(f3245,plain,(
    u1_struct_0(sK2) = sK3 ),
    inference(resolution,[],[f3244,f2971])).

fof(f2971,plain,
    ( ~ v1_tops_1(sK3,sK2)
    | u1_struct_0(sK2) = sK3 ),
    inference(backward_demodulation,[],[f979,f2969])).

fof(f2969,plain,(
    sK3 = k2_pre_topc(sK2,sK3) ),
    inference(resolution,[],[f2967,f584])).

fof(f584,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    | sK3 = k2_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f582,f52])).

fof(f52,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK2))
    & v3_tex_2(sK3,sK2)
    & ( v4_pre_topc(sK3,sK2)
      | v3_pre_topc(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_subset_1(X1,u1_struct_0(X0))
            & v3_tex_2(X1,X0)
            & ( v4_pre_topc(X1,X0)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(sK2))
          & v3_tex_2(X1,sK2)
          & ( v4_pre_topc(X1,sK2)
            | v3_pre_topc(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v3_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( v1_subset_1(X1,u1_struct_0(sK2))
        & v3_tex_2(X1,sK2)
        & ( v4_pre_topc(X1,sK2)
          | v3_pre_topc(X1,sK2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( v1_subset_1(sK3,u1_struct_0(sK2))
      & v3_tex_2(sK3,sK2)
      & ( v4_pre_topc(sK3,sK2)
        | v3_pre_topc(sK3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

fof(f582,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    | sK3 = k2_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f59,f53])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f2967,plain,(
    v4_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f2953,f2966])).

fof(f2966,plain,(
    v3_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2) ),
    inference(subsumption_resolution,[],[f2965,f92])).

fof(f92,plain,(
    sP0(sK2) ),
    inference(subsumption_resolution,[],[f91,f51])).

fof(f51,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,
    ( ~ v3_tdlat_3(sK2)
    | sP0(sK2) ),
    inference(resolution,[],[f89,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v3_tdlat_3(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v3_tdlat_3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f89,plain,(
    sP1(sK2) ),
    inference(subsumption_resolution,[],[f88,f52])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK2)
    | sP1(sK2) ),
    inference(resolution,[],[f74,f50])).

fof(f50,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f30,f36,f35])).

fof(f35,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f2965,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2)
    | ~ sP0(sK2) ),
    inference(resolution,[],[f2956,f162])).

fof(f162,plain,(
    ! [X2,X3] :
      ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(X2),X3),X2)
      | v3_pre_topc(k4_xboole_0(u1_struct_0(X2),X3),X2)
      | ~ sP0(X2) ) ),
    inference(resolution,[],[f70,f94])).

fof(f94,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f82,f75])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | v3_pre_topc(X2,X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ v3_pre_topc(sK4(X0),X0)
          & v4_pre_topc(sK4(X0),X0)
          & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_pre_topc(X2,X0)
            | ~ v4_pre_topc(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0),X0)
        & v4_pre_topc(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ~ v3_pre_topc(X1,X0)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_pre_topc(X2,X0)
            | ~ v4_pre_topc(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ~ v3_pre_topc(X1,X0)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f2956,plain,(
    v4_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2) ),
    inference(subsumption_resolution,[],[f2955,f52])).

fof(f2955,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f2954,f94])).

fof(f2954,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f2944,f166])).

fof(f166,plain,(
    v3_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f165,f54])).

fof(f54,plain,
    ( v3_pre_topc(sK3,sK2)
    | v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f165,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    | v3_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f163,f92])).

fof(f163,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    | v3_pre_topc(sK3,sK2)
    | ~ sP0(sK2) ),
    inference(resolution,[],[f70,f53])).

fof(f2944,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(superposition,[],[f64,f119])).

fof(f119,plain,(
    sK3 = k3_subset_1(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),sK3)) ),
    inference(forward_demodulation,[],[f116,f112])).

fof(f112,plain,(
    k4_xboole_0(u1_struct_0(sK2),sK3) = k3_subset_1(u1_struct_0(sK2),sK3) ),
    inference(resolution,[],[f78,f53])).

fof(f116,plain,(
    sK3 = k3_subset_1(u1_struct_0(sK2),k3_subset_1(u1_struct_0(sK2),sK3)) ),
    inference(resolution,[],[f79,f53])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f2953,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2)
    | v4_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f2952,f52])).

fof(f2952,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2)
    | v4_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f2943,f53])).

fof(f2943,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2)
    | v4_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(superposition,[],[f64,f112])).

fof(f979,plain,
    ( ~ v1_tops_1(sK3,sK2)
    | u1_struct_0(sK2) = k2_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f977,f52])).

fof(f977,plain,
    ( ~ v1_tops_1(sK3,sK2)
    | u1_struct_0(sK2) = k2_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f61,f53])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f3244,plain,(
    v1_tops_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f3243,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f3243,plain,
    ( v1_tops_1(sK3,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f3242,f50])).

fof(f3242,plain,
    ( v1_tops_1(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f3241,f52])).

fof(f3241,plain,
    ( v1_tops_1(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f3240,f166])).

fof(f3240,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | v1_tops_1(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f3238,f55])).

fof(f55,plain,(
    v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f3238,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v3_pre_topc(sK3,sK2)
    | v1_tops_1(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f67,f53])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | v1_tops_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

fof(f56,plain,(
    v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:24:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (19705)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (19704)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (19710)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (19695)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (19700)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (19699)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (19706)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (19696)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (19705)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f3292,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f3247,f253])).
% 0.21/0.47  fof(f253,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f252,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.47  % (19704)Refutation not found, incomplete strategy% (19704)------------------------------
% 0.21/0.47  % (19704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19704)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (19704)Memory used [KB]: 10746
% 0.21/0.47  % (19704)Time elapsed: 0.076 s
% 0.21/0.47  % (19704)------------------------------
% 0.21/0.47  % (19704)------------------------------
% 0.21/0.47  fof(f252,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~v1_subset_1(X0,X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f246,f149])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f110,f138])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f124,f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(resolution,[],[f66,f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.47    inference(superposition,[],[f83,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f76,f77,f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 0.21/0.47    inference(resolution,[],[f78,f95])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X2))) )),
% 0.21/0.47    inference(resolution,[],[f82,f84])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.47    inference(superposition,[],[f75,f58])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.47    inference(nnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.47  fof(f246,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(k3_subset_1(X0,X0)) | ~v1_subset_1(X0,X0)) )),
% 0.21/0.47    inference(resolution,[],[f245,f95])).
% 0.21/0.47  fof(f245,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(k3_subset_1(X0,X1)) | ~v1_subset_1(X1,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f80,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & v1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k3_subset_1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).
% 0.21/0.47  fof(f3247,plain,(
% 0.21/0.47    v1_subset_1(sK3,sK3)),
% 0.21/0.47    inference(backward_demodulation,[],[f56,f3245])).
% 0.21/0.47  fof(f3245,plain,(
% 0.21/0.47    u1_struct_0(sK2) = sK3),
% 0.21/0.47    inference(resolution,[],[f3244,f2971])).
% 0.21/0.47  fof(f2971,plain,(
% 0.21/0.47    ~v1_tops_1(sK3,sK2) | u1_struct_0(sK2) = sK3),
% 0.21/0.47    inference(backward_demodulation,[],[f979,f2969])).
% 0.21/0.47  fof(f2969,plain,(
% 0.21/0.47    sK3 = k2_pre_topc(sK2,sK3)),
% 0.21/0.47    inference(resolution,[],[f2967,f584])).
% 0.21/0.47  fof(f584,plain,(
% 0.21/0.47    ~v4_pre_topc(sK3,sK2) | sK3 = k2_pre_topc(sK2,sK3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f582,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    l1_pre_topc(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    (v1_subset_1(sK3,u1_struct_0(sK2)) & v3_tex_2(sK3,sK2) & (v4_pre_topc(sK3,sK2) | v3_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f39,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v1_subset_1(X1,u1_struct_0(sK2)) & v3_tex_2(X1,sK2) & (v4_pre_topc(X1,sK2) | v3_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ? [X1] : (v1_subset_1(X1,u1_struct_0(sK2)) & v3_tex_2(X1,sK2) & (v4_pre_topc(X1,sK2) | v3_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => (v1_subset_1(sK3,u1_struct_0(sK2)) & v3_tex_2(sK3,sK2) & (v4_pre_topc(sK3,sK2) | v3_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f17])).
% 0.21/0.48  fof(f17,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).
% 0.21/0.48  fof(f582,plain,(
% 0.21/0.48    ~v4_pre_topc(sK3,sK2) | sK3 = k2_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2)),
% 0.21/0.48    inference(resolution,[],[f59,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.48  fof(f2967,plain,(
% 0.21/0.48    v4_pre_topc(sK3,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f2953,f2966])).
% 0.21/0.48  fof(f2966,plain,(
% 0.21/0.48    v3_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f2965,f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    sP0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f91,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    v3_tdlat_3(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ~v3_tdlat_3(sK2) | sP0(sK2)),
% 0.21/0.48    inference(resolution,[],[f89,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0] : (~sP1(X0) | ~v3_tdlat_3(X0) | sP0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ! [X0] : (((v3_tdlat_3(X0) | ~sP0(X0)) & (sP0(X0) | ~v3_tdlat_3(X0))) | ~sP1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0] : ((v3_tdlat_3(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    sP1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f88,f52])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ~l1_pre_topc(sK2) | sP1(sK2)),
% 0.21/0.48    inference(resolution,[],[f74,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    v2_pre_topc(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | sP1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0] : (sP1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(definition_folding,[],[f30,f36,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0] : (sP0(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.21/0.48  fof(f2965,plain,(
% 0.21/0.48    v3_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2) | ~sP0(sK2)),
% 0.21/0.48    inference(resolution,[],[f2956,f162])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~v4_pre_topc(k4_xboole_0(u1_struct_0(X2),X3),X2) | v3_pre_topc(k4_xboole_0(u1_struct_0(X2),X3),X2) | ~sP0(X2)) )),
% 0.21/0.48    inference(resolution,[],[f70,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(resolution,[],[f82,f75])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | v3_pre_topc(X2,X0) | ~sP0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ! [X0] : ((sP0(X0) | (~v3_pre_topc(sK4(X0),X0) & v4_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK4(X0),X0) & v4_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ! [X0] : ((sP0(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.21/0.48    inference(rectify,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ! [X0] : ((sP0(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f35])).
% 0.21/0.48  fof(f2956,plain,(
% 0.21/0.48    v4_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f2955,f52])).
% 0.21/0.48  fof(f2955,plain,(
% 0.21/0.48    v4_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2) | ~l1_pre_topc(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f2954,f94])).
% 0.21/0.48  fof(f2954,plain,(
% 0.21/0.48    v4_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f2944,f166])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    v3_pre_topc(sK3,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f165,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    v3_pre_topc(sK3,sK2) | v4_pre_topc(sK3,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    ~v4_pre_topc(sK3,sK2) | v3_pre_topc(sK3,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f163,f92])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ~v4_pre_topc(sK3,sK2) | v3_pre_topc(sK3,sK2) | ~sP0(sK2)),
% 0.21/0.48    inference(resolution,[],[f70,f53])).
% 0.21/0.48  fof(f2944,plain,(
% 0.21/0.48    ~v3_pre_topc(sK3,sK2) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.21/0.48    inference(superposition,[],[f64,f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    sK3 = k3_subset_1(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),sK3))),
% 0.21/0.48    inference(forward_demodulation,[],[f116,f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    k4_xboole_0(u1_struct_0(sK2),sK3) = k3_subset_1(u1_struct_0(sK2),sK3)),
% 0.21/0.48    inference(resolution,[],[f78,f53])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    sK3 = k3_subset_1(u1_struct_0(sK2),k3_subset_1(u1_struct_0(sK2),sK3))),
% 0.21/0.48    inference(resolution,[],[f79,f53])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.21/0.48  fof(f2953,plain,(
% 0.21/0.48    ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2) | v4_pre_topc(sK3,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f2952,f52])).
% 0.21/0.48  fof(f2952,plain,(
% 0.21/0.48    ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2) | v4_pre_topc(sK3,sK2) | ~l1_pre_topc(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f2943,f53])).
% 0.21/0.48  fof(f2943,plain,(
% 0.21/0.48    ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK2),sK3),sK2) | v4_pre_topc(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.21/0.48    inference(superposition,[],[f64,f112])).
% 0.21/0.48  fof(f979,plain,(
% 0.21/0.48    ~v1_tops_1(sK3,sK2) | u1_struct_0(sK2) = k2_pre_topc(sK2,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f977,f52])).
% 0.21/0.48  fof(f977,plain,(
% 0.21/0.48    ~v1_tops_1(sK3,sK2) | u1_struct_0(sK2) = k2_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2)),
% 0.21/0.48    inference(resolution,[],[f61,f53])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 0.21/0.48  fof(f3244,plain,(
% 0.21/0.48    v1_tops_1(sK3,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f3243,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ~v2_struct_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f3243,plain,(
% 0.21/0.48    v1_tops_1(sK3,sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f3242,f50])).
% 0.21/0.48  fof(f3242,plain,(
% 0.21/0.48    v1_tops_1(sK3,sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f3241,f52])).
% 0.21/0.48  fof(f3241,plain,(
% 0.21/0.48    v1_tops_1(sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f3240,f166])).
% 0.21/0.48  fof(f3240,plain,(
% 0.21/0.48    ~v3_pre_topc(sK3,sK2) | v1_tops_1(sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f3238,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    v3_tex_2(sK3,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f3238,plain,(
% 0.21/0.48    ~v3_tex_2(sK3,sK2) | ~v3_pre_topc(sK3,sK2) | v1_tops_1(sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(resolution,[],[f67,f53])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | v1_tops_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    v1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (19705)------------------------------
% 0.21/0.48  % (19705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (19705)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (19705)Memory used [KB]: 2686
% 0.21/0.48  % (19705)Time elapsed: 0.057 s
% 0.21/0.48  % (19705)------------------------------
% 0.21/0.48  % (19705)------------------------------
% 0.21/0.48  % (19692)Success in time 0.119 s
%------------------------------------------------------------------------------
