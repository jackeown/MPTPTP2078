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
% DateTime   : Thu Dec  3 13:12:14 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 247 expanded)
%              Number of leaves         :   22 (  77 expanded)
%              Depth                    :   18
%              Number of atoms          :  300 (1132 expanded)
%              Number of equality atoms :   79 ( 309 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f128,f130,f149,f163,f166,f169,f176,f197])).

fof(f197,plain,
    ( spl2_2
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl2_2
    | ~ spl2_9 ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | spl2_2
    | ~ spl2_9 ),
    inference(superposition,[],[f63,f192])).

fof(f192,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f190,f175])).

fof(f175,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl2_9
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f190,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f164,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f32,plain,
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

fof(f33,plain,
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

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f42,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f63,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f176,plain,
    ( spl2_9
    | ~ spl2_8
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f168,f58,f160,f173])).

fof(f160,plain,
    ( spl2_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f58,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f168,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f60,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f43,f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f60,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f169,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f60,f67])).

fof(f67,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f39,f64])).

fof(f64,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f39,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f166,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f162,f37])).

fof(f162,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f160])).

fof(f163,plain,
    ( ~ spl2_6
    | ~ spl2_3
    | ~ spl2_8
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f156,f126,f62,f58,f160,f122,f141])).

fof(f141,plain,
    ( spl2_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f122,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f126,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f156,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(superposition,[],[f48,f153])).

fof(f153,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f151,f133])).

fof(f133,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f131,f78])).

fof(f78,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f76,f40])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f76,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f54,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f74,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f74,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f53,f71])).

fof(f71,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f69,f64])).

fof(f69,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f56,f37])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f51,f46])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f131,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_4 ),
    inference(resolution,[],[f127,f37])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f151,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f150,f37])).

fof(f150,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f41,f36])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f149,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f143,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f143,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f141])).

fof(f130,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f124,f36])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f128,plain,
    ( ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f119,f126,f122])).

fof(f119,plain,(
    ! [X0] :
      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f116,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f52,f37])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f65,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f38,f62,f58])).

fof(f38,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n022.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 19:47:11 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.41  % (22838)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.18/0.45  % (22839)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.18/0.45  % (22830)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.18/0.46  % (22832)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.18/0.46  % (22837)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.18/0.46  % (22843)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.18/0.46  % (22831)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.18/0.46  % (22836)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.18/0.47  % (22833)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.18/0.47  % (22845)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.18/0.47  % (22832)Refutation found. Thanks to Tanya!
% 0.18/0.47  % SZS status Theorem for theBenchmark
% 0.18/0.47  % SZS output start Proof for theBenchmark
% 0.18/0.47  fof(f198,plain,(
% 0.18/0.47    $false),
% 0.18/0.47    inference(avatar_sat_refutation,[],[f65,f128,f130,f149,f163,f166,f169,f176,f197])).
% 0.18/0.47  fof(f197,plain,(
% 0.18/0.47    spl2_2 | ~spl2_9),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f196])).
% 0.18/0.47  fof(f196,plain,(
% 0.18/0.47    $false | (spl2_2 | ~spl2_9)),
% 0.18/0.47    inference(trivial_inequality_removal,[],[f194])).
% 0.18/0.47  fof(f194,plain,(
% 0.18/0.47    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | (spl2_2 | ~spl2_9)),
% 0.18/0.47    inference(superposition,[],[f63,f192])).
% 0.18/0.47  fof(f192,plain,(
% 0.18/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_9),
% 0.18/0.47    inference(forward_demodulation,[],[f190,f175])).
% 0.18/0.47  fof(f175,plain,(
% 0.18/0.47    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_9),
% 0.18/0.47    inference(avatar_component_clause,[],[f173])).
% 0.18/0.47  fof(f173,plain,(
% 0.18/0.47    spl2_9 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.18/0.47  fof(f190,plain,(
% 0.18/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.18/0.47    inference(resolution,[],[f164,f37])).
% 0.18/0.47  fof(f37,plain,(
% 0.18/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.47    inference(cnf_transformation,[],[f34])).
% 0.18/0.47  fof(f34,plain,(
% 0.18/0.47    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 0.18/0.47  fof(f32,plain,(
% 0.18/0.47    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f33,plain,(
% 0.18/0.47    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f31,plain,(
% 0.18/0.47    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.18/0.47    inference(flattening,[],[f30])).
% 0.18/0.47  fof(f30,plain,(
% 0.18/0.47    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.18/0.47    inference(nnf_transformation,[],[f17])).
% 0.18/0.47  fof(f17,plain,(
% 0.18/0.47    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.18/0.47    inference(flattening,[],[f16])).
% 0.18/0.47  fof(f16,plain,(
% 0.18/0.47    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.18/0.47    inference(ennf_transformation,[],[f14])).
% 0.18/0.47  fof(f14,negated_conjecture,(
% 0.18/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.18/0.47    inference(negated_conjecture,[],[f13])).
% 0.18/0.47  fof(f13,conjecture,(
% 0.18/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.18/0.47  fof(f164,plain,(
% 0.18/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) )),
% 0.18/0.47    inference(resolution,[],[f42,f36])).
% 0.18/0.47  fof(f36,plain,(
% 0.18/0.47    l1_pre_topc(sK0)),
% 0.18/0.47    inference(cnf_transformation,[],[f34])).
% 0.18/0.47  fof(f42,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f19])).
% 0.18/0.47  fof(f19,plain,(
% 0.18/0.47    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.47    inference(ennf_transformation,[],[f11])).
% 0.18/0.47  fof(f11,axiom,(
% 0.18/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.18/0.47  fof(f63,plain,(
% 0.18/0.47    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 0.18/0.47    inference(avatar_component_clause,[],[f62])).
% 0.18/0.47  fof(f62,plain,(
% 0.18/0.47    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.18/0.47  fof(f176,plain,(
% 0.18/0.47    spl2_9 | ~spl2_8 | ~spl2_1),
% 0.18/0.47    inference(avatar_split_clause,[],[f168,f58,f160,f173])).
% 0.18/0.47  fof(f160,plain,(
% 0.18/0.47    spl2_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.18/0.47  fof(f58,plain,(
% 0.18/0.47    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.18/0.47  fof(f168,plain,(
% 0.18/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | ~spl2_1),
% 0.18/0.47    inference(resolution,[],[f60,f83])).
% 0.18/0.47  fof(f83,plain,(
% 0.18/0.47    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) )),
% 0.18/0.47    inference(resolution,[],[f43,f36])).
% 0.18/0.47  fof(f43,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 0.18/0.47    inference(cnf_transformation,[],[f21])).
% 0.18/0.47  fof(f21,plain,(
% 0.18/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.47    inference(flattening,[],[f20])).
% 0.18/0.47  fof(f20,plain,(
% 0.18/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.47    inference(ennf_transformation,[],[f8])).
% 0.18/0.47  fof(f8,axiom,(
% 0.18/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.18/0.47  fof(f60,plain,(
% 0.18/0.47    v4_pre_topc(sK1,sK0) | ~spl2_1),
% 0.18/0.47    inference(avatar_component_clause,[],[f58])).
% 0.18/0.47  fof(f169,plain,(
% 0.18/0.47    ~spl2_1 | ~spl2_2),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f167])).
% 0.18/0.47  fof(f167,plain,(
% 0.18/0.47    $false | (~spl2_1 | ~spl2_2)),
% 0.18/0.47    inference(resolution,[],[f60,f67])).
% 0.18/0.47  fof(f67,plain,(
% 0.18/0.47    ~v4_pre_topc(sK1,sK0) | ~spl2_2),
% 0.18/0.47    inference(trivial_inequality_removal,[],[f66])).
% 0.18/0.47  fof(f66,plain,(
% 0.18/0.47    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | ~spl2_2),
% 0.18/0.47    inference(forward_demodulation,[],[f39,f64])).
% 0.18/0.47  fof(f64,plain,(
% 0.18/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 0.18/0.47    inference(avatar_component_clause,[],[f62])).
% 0.18/0.47  fof(f39,plain,(
% 0.18/0.47    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.18/0.47    inference(cnf_transformation,[],[f34])).
% 0.18/0.47  fof(f166,plain,(
% 0.18/0.47    spl2_8),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f165])).
% 0.18/0.47  fof(f165,plain,(
% 0.18/0.47    $false | spl2_8),
% 0.18/0.47    inference(resolution,[],[f162,f37])).
% 0.18/0.47  fof(f162,plain,(
% 0.18/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_8),
% 0.18/0.47    inference(avatar_component_clause,[],[f160])).
% 0.18/0.47  fof(f163,plain,(
% 0.18/0.47    ~spl2_6 | ~spl2_3 | ~spl2_8 | spl2_1 | ~spl2_2 | ~spl2_4),
% 0.18/0.47    inference(avatar_split_clause,[],[f156,f126,f62,f58,f160,f122,f141])).
% 0.18/0.47  fof(f141,plain,(
% 0.18/0.47    spl2_6 <=> v2_pre_topc(sK0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.18/0.47  fof(f122,plain,(
% 0.18/0.47    spl2_3 <=> l1_pre_topc(sK0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.18/0.47  fof(f126,plain,(
% 0.18/0.47    spl2_4 <=> ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.18/0.47  fof(f156,plain,(
% 0.18/0.47    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl2_2 | ~spl2_4)),
% 0.18/0.47    inference(superposition,[],[f48,f153])).
% 0.18/0.47  fof(f153,plain,(
% 0.18/0.47    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_4)),
% 0.18/0.47    inference(forward_demodulation,[],[f151,f133])).
% 0.18/0.47  fof(f133,plain,(
% 0.18/0.47    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_4)),
% 0.18/0.47    inference(forward_demodulation,[],[f131,f78])).
% 0.18/0.47  fof(f78,plain,(
% 0.18/0.47    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.18/0.47    inference(forward_demodulation,[],[f76,f40])).
% 0.18/0.47  fof(f40,plain,(
% 0.18/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.18/0.47    inference(cnf_transformation,[],[f3])).
% 0.18/0.47  fof(f3,axiom,(
% 0.18/0.47    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.18/0.47  fof(f76,plain,(
% 0.18/0.47    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_xboole_0) | ~spl2_2),
% 0.18/0.47    inference(superposition,[],[f54,f75])).
% 0.18/0.47  fof(f75,plain,(
% 0.18/0.47    k1_xboole_0 = k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),sK1)) | ~spl2_2),
% 0.18/0.47    inference(resolution,[],[f74,f55])).
% 0.18/0.47  fof(f55,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.18/0.47    inference(definition_unfolding,[],[f50,f46])).
% 0.18/0.47  fof(f46,plain,(
% 0.18/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f2])).
% 0.18/0.47  fof(f2,axiom,(
% 0.18/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.18/0.47  fof(f50,plain,(
% 0.18/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f26])).
% 0.18/0.47  fof(f26,plain,(
% 0.18/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.18/0.47    inference(ennf_transformation,[],[f15])).
% 0.18/0.47  fof(f15,plain,(
% 0.18/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.18/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.18/0.47  fof(f1,axiom,(
% 0.18/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.18/0.47  fof(f74,plain,(
% 0.18/0.47    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_2),
% 0.18/0.47    inference(superposition,[],[f53,f71])).
% 0.18/0.47  fof(f71,plain,(
% 0.18/0.47    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | ~spl2_2),
% 0.18/0.47    inference(superposition,[],[f69,f64])).
% 0.18/0.47  fof(f69,plain,(
% 0.18/0.47    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) )),
% 0.18/0.47    inference(resolution,[],[f56,f37])).
% 0.18/0.47  fof(f56,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 0.18/0.47    inference(definition_unfolding,[],[f51,f46])).
% 0.18/0.47  fof(f51,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f27])).
% 0.18/0.47  fof(f27,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.47    inference(ennf_transformation,[],[f7])).
% 0.18/0.47  fof(f7,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.18/0.47  fof(f53,plain,(
% 0.18/0.47    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.18/0.47    inference(definition_unfolding,[],[f45,f46])).
% 0.18/0.47  fof(f45,plain,(
% 0.18/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f4])).
% 0.18/0.47  fof(f4,axiom,(
% 0.18/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.18/0.47  fof(f54,plain,(
% 0.18/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.18/0.47    inference(definition_unfolding,[],[f47,f46])).
% 0.18/0.47  fof(f47,plain,(
% 0.18/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f5])).
% 0.18/0.47  fof(f5,axiom,(
% 0.18/0.47    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.18/0.47  fof(f131,plain,(
% 0.18/0.47    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_4),
% 0.18/0.47    inference(resolution,[],[f127,f37])).
% 0.18/0.47  fof(f127,plain,(
% 0.18/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))) ) | ~spl2_4),
% 0.18/0.47    inference(avatar_component_clause,[],[f126])).
% 0.18/0.47  fof(f151,plain,(
% 0.18/0.47    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)),
% 0.18/0.47    inference(resolution,[],[f150,f37])).
% 0.18/0.47  fof(f150,plain,(
% 0.18/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 0.18/0.47    inference(resolution,[],[f41,f36])).
% 0.18/0.47  fof(f41,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f18])).
% 0.18/0.47  fof(f18,plain,(
% 0.18/0.47    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.47    inference(ennf_transformation,[],[f12])).
% 0.18/0.47  fof(f12,axiom,(
% 0.18/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.18/0.47  fof(f48,plain,(
% 0.18/0.47    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f23])).
% 0.18/0.47  fof(f23,plain,(
% 0.18/0.47    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.18/0.47    inference(flattening,[],[f22])).
% 0.18/0.47  fof(f22,plain,(
% 0.18/0.47    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.18/0.47    inference(ennf_transformation,[],[f10])).
% 0.18/0.47  fof(f10,axiom,(
% 0.18/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.18/0.47  fof(f149,plain,(
% 0.18/0.47    spl2_6),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f148])).
% 0.18/0.47  fof(f148,plain,(
% 0.18/0.47    $false | spl2_6),
% 0.18/0.47    inference(resolution,[],[f143,f35])).
% 0.18/0.47  fof(f35,plain,(
% 0.18/0.47    v2_pre_topc(sK0)),
% 0.18/0.47    inference(cnf_transformation,[],[f34])).
% 0.18/0.47  fof(f143,plain,(
% 0.18/0.47    ~v2_pre_topc(sK0) | spl2_6),
% 0.18/0.47    inference(avatar_component_clause,[],[f141])).
% 0.18/0.47  fof(f130,plain,(
% 0.18/0.47    spl2_3),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f129])).
% 0.18/0.47  fof(f129,plain,(
% 0.18/0.47    $false | spl2_3),
% 0.18/0.47    inference(resolution,[],[f124,f36])).
% 0.18/0.47  fof(f124,plain,(
% 0.18/0.47    ~l1_pre_topc(sK0) | spl2_3),
% 0.18/0.47    inference(avatar_component_clause,[],[f122])).
% 0.18/0.47  fof(f128,plain,(
% 0.18/0.47    ~spl2_3 | spl2_4),
% 0.18/0.47    inference(avatar_split_clause,[],[f119,f126,f122])).
% 0.18/0.47  fof(f119,plain,(
% 0.18/0.47    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.18/0.47    inference(resolution,[],[f116,f49])).
% 0.18/0.47  fof(f49,plain,(
% 0.18/0.47    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f25])).
% 0.18/0.47  fof(f25,plain,(
% 0.18/0.47    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.18/0.47    inference(flattening,[],[f24])).
% 0.18/0.47  fof(f24,plain,(
% 0.18/0.47    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.18/0.47    inference(ennf_transformation,[],[f9])).
% 0.18/0.47  fof(f9,axiom,(
% 0.18/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.18/0.47  fof(f116,plain,(
% 0.18/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)) )),
% 0.18/0.47    inference(resolution,[],[f52,f37])).
% 0.18/0.47  fof(f52,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f29])).
% 0.18/0.47  fof(f29,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.47    inference(flattening,[],[f28])).
% 0.18/0.47  fof(f28,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.18/0.47    inference(ennf_transformation,[],[f6])).
% 0.18/0.47  fof(f6,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.18/0.47  fof(f65,plain,(
% 0.18/0.47    spl2_1 | spl2_2),
% 0.18/0.47    inference(avatar_split_clause,[],[f38,f62,f58])).
% 0.18/0.47  fof(f38,plain,(
% 0.18/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.18/0.47    inference(cnf_transformation,[],[f34])).
% 0.18/0.47  % SZS output end Proof for theBenchmark
% 0.18/0.47  % (22832)------------------------------
% 0.18/0.47  % (22832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (22832)Termination reason: Refutation
% 0.18/0.47  
% 0.18/0.47  % (22832)Memory used [KB]: 6140
% 0.18/0.47  % (22832)Time elapsed: 0.037 s
% 0.18/0.47  % (22832)------------------------------
% 0.18/0.47  % (22832)------------------------------
% 0.18/0.47  % (22834)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.18/0.47  % (22829)Success in time 0.128 s
%------------------------------------------------------------------------------
