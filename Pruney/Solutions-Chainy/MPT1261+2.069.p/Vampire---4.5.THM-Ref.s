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
% DateTime   : Thu Dec  3 13:11:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 246 expanded)
%              Number of leaves         :   22 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  290 (1124 expanded)
%              Number of equality atoms :   80 ( 312 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f100,f102,f111,f134,f136,f139,f145,f174])).

% (27483)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f174,plain,
    ( spl2_2
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl2_2
    | ~ spl2_9 ),
    inference(trivial_inequality_removal,[],[f171])).

fof(f171,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | spl2_2
    | ~ spl2_9 ),
    inference(superposition,[],[f60,f169])).

fof(f169,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f167,f144])).

fof(f144,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl2_9
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f167,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f166,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f39,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f60,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f145,plain,
    ( spl2_9
    | ~ spl2_8
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f138,f55,f131,f142])).

fof(f131,plain,
    ( spl2_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f55,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f138,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f57,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f40,f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f57,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f139,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f57,f64])).

fof(f64,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f63])).

fof(f63,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f37,f61])).

fof(f61,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f37,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f136,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f133,f35])).

fof(f133,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f134,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8
    | spl2_1
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f127,f109,f59,f55,f131,f92,f88])).

fof(f88,plain,
    ( spl2_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f92,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f109,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f127,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(superposition,[],[f47,f124])).

fof(f124,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f122,f114])).

fof(f114,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f112,f77])).

fof(f77,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f75,f66])).

fof(f66,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(superposition,[],[f65,f61])).

fof(f65,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f49,f35])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f75,plain,(
    ! [X2,X3] : k3_tarski(k2_tarski(X2,k4_xboole_0(X2,X3))) = X2 ),
    inference(forward_demodulation,[],[f73,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f73,plain,(
    ! [X2,X3] : k3_tarski(k2_tarski(k4_xboole_0(X2,X3),X2)) = X2 ),
    inference(superposition,[],[f71,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f45,f43,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f52,f42])).

fof(f52,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f46,f43,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f112,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(resolution,[],[f110,f35])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f122,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f121,f35])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f38,f34])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f111,plain,
    ( ~ spl2_4
    | spl2_6 ),
    inference(avatar_split_clause,[],[f106,f109,f92])).

fof(f106,plain,(
    ! [X0] :
      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f103,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)) ) ),
    inference(resolution,[],[f53,f35])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f50,f43])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f102,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f94,f34])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f100,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f90,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f62,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f36,f59,f55])).

fof(f36,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:17:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (27482)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (27492)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (27488)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (27480)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (27482)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f62,f100,f102,f111,f134,f136,f139,f145,f174])).
% 0.22/0.49  % (27483)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    spl2_2 | ~spl2_9),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f173])).
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    $false | (spl2_2 | ~spl2_9)),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f171])).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | (spl2_2 | ~spl2_9)),
% 0.22/0.49    inference(superposition,[],[f60,f169])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_9),
% 0.22/0.49    inference(forward_demodulation,[],[f167,f144])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f142])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    spl2_9 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f166,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f13])).
% 0.22/0.49  fof(f13,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) )),
% 0.22/0.49    inference(resolution,[],[f39,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    spl2_9 | ~spl2_8 | ~spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f138,f55,f131,f142])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    spl2_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | ~spl2_1),
% 0.22/0.49    inference(resolution,[],[f57,f85])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) )),
% 0.22/0.49    inference(resolution,[],[f40,f34])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    v4_pre_topc(sK1,sK0) | ~spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f55])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ~spl2_1 | ~spl2_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f137])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    $false | (~spl2_1 | ~spl2_2)),
% 0.22/0.49    inference(resolution,[],[f57,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ~v4_pre_topc(sK1,sK0) | ~spl2_2),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | ~spl2_2),
% 0.22/0.49    inference(forward_demodulation,[],[f37,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f59])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    spl2_8),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f135])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    $false | spl2_8),
% 0.22/0.49    inference(resolution,[],[f133,f35])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f131])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    ~spl2_3 | ~spl2_4 | ~spl2_8 | spl2_1 | ~spl2_2 | ~spl2_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f127,f109,f59,f55,f131,f92,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    spl2_3 <=> v2_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    spl2_4 <=> l1_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl2_6 <=> ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl2_2 | ~spl2_6)),
% 0.22/0.49    inference(superposition,[],[f47,f124])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_6)),
% 0.22/0.49    inference(forward_demodulation,[],[f122,f114])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_6)),
% 0.22/0.49    inference(forward_demodulation,[],[f112,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_2),
% 0.22/0.49    inference(superposition,[],[f75,f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 0.22/0.49    inference(superposition,[],[f65,f61])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 0.22/0.49    inference(resolution,[],[f49,f35])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k3_tarski(k2_tarski(X2,k4_xboole_0(X2,X3))) = X2) )),
% 0.22/0.49    inference(forward_demodulation,[],[f73,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k3_tarski(k2_tarski(k4_xboole_0(X2,X3),X2)) = X2) )),
% 0.22/0.49    inference(superposition,[],[f71,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f45,f43,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 0.22/0.49    inference(forward_demodulation,[],[f52,f42])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0) )),
% 0.22/0.49    inference(definition_unfolding,[],[f46,f43,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_6),
% 0.22/0.49    inference(resolution,[],[f110,f35])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))) ) | ~spl2_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f109])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)),
% 0.22/0.49    inference(resolution,[],[f121,f35])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 0.22/0.49    inference(resolution,[],[f38,f34])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    ~spl2_4 | spl2_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f106,f109,f92])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.22/0.49    inference(resolution,[],[f103,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))) )),
% 0.22/0.49    inference(resolution,[],[f53,f35])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f50,f43])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl2_4),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f101])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    $false | spl2_4),
% 0.22/0.49    inference(resolution,[],[f94,f34])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | spl2_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f92])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl2_3),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f99])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    $false | spl2_3),
% 0.22/0.49    inference(resolution,[],[f90,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | spl2_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f88])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl2_1 | spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f59,f55])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (27482)------------------------------
% 0.22/0.49  % (27482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27482)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (27482)Memory used [KB]: 6140
% 0.22/0.49  % (27482)Time elapsed: 0.072 s
% 0.22/0.49  % (27482)------------------------------
% 0.22/0.49  % (27482)------------------------------
% 0.22/0.50  % (27479)Success in time 0.13 s
%------------------------------------------------------------------------------
