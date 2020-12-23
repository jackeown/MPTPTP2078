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
% DateTime   : Thu Dec  3 13:12:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 413 expanded)
%              Number of leaves         :   26 ( 125 expanded)
%              Depth                    :   21
%              Number of atoms          :  341 (1536 expanded)
%              Number of equality atoms :   95 ( 459 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f759,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f236,f238,f576,f578,f581,f584,f589,f755])).

fof(f755,plain,
    ( spl2_2
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f754])).

fof(f754,plain,
    ( $false
    | spl2_2
    | ~ spl2_7 ),
    inference(trivial_inequality_removal,[],[f727])).

fof(f727,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | spl2_2
    | ~ spl2_7 ),
    inference(superposition,[],[f77,f726])).

fof(f726,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f725,f588])).

fof(f588,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f586])).

fof(f586,plain,
    ( spl2_7
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f725,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f721,f45])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f40,plain,
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

fof(f41,plain,
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

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f721,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f50,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f77,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f589,plain,
    ( spl2_7
    | ~ spl2_6
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f583,f72,f573,f586])).

fof(f573,plain,
    ( spl2_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f72,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f583,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f74,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f51,f44])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f74,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f584,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f582])).

fof(f582,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f74,f81])).

fof(f81,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f47,f78])).

fof(f78,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f47,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f581,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f575,f45])).

fof(f575,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f573])).

fof(f578,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f577])).

fof(f577,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f571,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f571,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f569])).

fof(f569,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f576,plain,
    ( ~ spl2_5
    | ~ spl2_3
    | ~ spl2_6
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f566,f234,f76,f72,f573,f230,f569])).

fof(f230,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f234,plain,
    ( spl2_4
  <=> ! [X2] :
        ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f566,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(superposition,[],[f61,f564])).

fof(f564,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f563,f478])).

fof(f478,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f242,f476])).

fof(f476,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f475,f114])).

fof(f114,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(resolution,[],[f112,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) ),
    inference(resolution,[],[f82,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) ),
    inference(forward_demodulation,[],[f60,f48])).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f112,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f109,f78])).

fof(f109,plain,(
    ! [X1] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X1),sK1) ),
    inference(superposition,[],[f67,f107])).

fof(f107,plain,(
    ! [X9] : k7_subset_1(u1_struct_0(sK0),sK1,X9) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X9))) ),
    inference(resolution,[],[f70,f45])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f64,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f56,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f475,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f456,f125])).

fof(f125,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f123,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f123,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f68,f113])).

fof(f113,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))
    | ~ spl2_2 ),
    inference(resolution,[],[f112,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(resolution,[],[f69,f63])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f57,f66])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f456,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(resolution,[],[f358,f112])).

fof(f358,plain,
    ( ! [X5] :
        ( ~ r1_tarski(X5,sK1)
        | k4_subset_1(sK1,X5,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(X5,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) )
    | ~ spl2_2 ),
    inference(resolution,[],[f344,f124])).

fof(f124,plain,
    ( r1_tarski(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f67,f113])).

fof(f344,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | ~ r1_tarski(X1,X0)
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f144,f63])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f65,f63])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f242,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_4 ),
    inference(resolution,[],[f235,f45])).

fof(f235,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2)) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f234])).

fof(f563,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f559,f45])).

fof(f559,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f49,f44])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f238,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f232,f44])).

fof(f232,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f230])).

fof(f236,plain,
    ( ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f152,f234,f230])).

fof(f152,plain,(
    ! [X2] :
      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f147,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f147,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),sK1,X9) = k2_xboole_0(sK1,X9) ) ),
    inference(resolution,[],[f65,f45])).

fof(f79,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f46,f76,f72])).

fof(f46,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:01:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (12832)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.45  % (12826)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (12825)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (12835)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (12834)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (12833)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (12827)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (12836)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (12828)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (12831)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (12837)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (12839)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (12840)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (12824)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (12838)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (12830)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (12829)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (12825)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f759,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f79,f236,f238,f576,f578,f581,f584,f589,f755])).
% 0.21/0.52  fof(f755,plain,(
% 0.21/0.52    spl2_2 | ~spl2_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f754])).
% 0.21/0.52  fof(f754,plain,(
% 0.21/0.52    $false | (spl2_2 | ~spl2_7)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f727])).
% 0.21/0.52  fof(f727,plain,(
% 0.21/0.52    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | (spl2_2 | ~spl2_7)),
% 0.21/0.52    inference(superposition,[],[f77,f726])).
% 0.21/0.52  fof(f726,plain,(
% 0.21/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_7),
% 0.21/0.52    inference(forward_demodulation,[],[f725,f588])).
% 0.21/0.52  fof(f588,plain,(
% 0.21/0.52    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f586])).
% 0.21/0.52  fof(f586,plain,(
% 0.21/0.52    spl2_7 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.52  fof(f725,plain,(
% 0.21/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.21/0.52    inference(resolution,[],[f721,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f18])).
% 0.21/0.52  fof(f18,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 0.21/0.52  fof(f721,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) )),
% 0.21/0.52    inference(resolution,[],[f50,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f589,plain,(
% 0.21/0.52    spl2_7 | ~spl2_6 | ~spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f583,f72,f573,f586])).
% 0.21/0.52  fof(f573,plain,(
% 0.21/0.52    spl2_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f583,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | ~spl2_1),
% 0.21/0.52    inference(resolution,[],[f74,f102])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) )),
% 0.21/0.52    inference(resolution,[],[f51,f44])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    v4_pre_topc(sK1,sK0) | ~spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f72])).
% 0.21/0.52  fof(f584,plain,(
% 0.21/0.52    ~spl2_1 | ~spl2_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f582])).
% 0.21/0.52  fof(f582,plain,(
% 0.21/0.52    $false | (~spl2_1 | ~spl2_2)),
% 0.21/0.52    inference(resolution,[],[f74,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ~v4_pre_topc(sK1,sK0) | ~spl2_2),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | ~spl2_2),
% 0.21/0.52    inference(forward_demodulation,[],[f47,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f76])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f581,plain,(
% 0.21/0.52    spl2_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f579])).
% 0.21/0.52  fof(f579,plain,(
% 0.21/0.52    $false | spl2_6),
% 0.21/0.52    inference(resolution,[],[f575,f45])).
% 0.21/0.52  fof(f575,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f573])).
% 0.21/0.52  fof(f578,plain,(
% 0.21/0.52    spl2_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f577])).
% 0.21/0.52  fof(f577,plain,(
% 0.21/0.52    $false | spl2_5),
% 0.21/0.52    inference(resolution,[],[f571,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f571,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | spl2_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f569])).
% 0.21/0.52  fof(f569,plain,(
% 0.21/0.52    spl2_5 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.52  fof(f576,plain,(
% 0.21/0.52    ~spl2_5 | ~spl2_3 | ~spl2_6 | spl2_1 | ~spl2_2 | ~spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f566,f234,f76,f72,f573,f230,f569])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    spl2_3 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    spl2_4 <=> ! [X2] : (k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.52  fof(f566,plain,(
% 0.21/0.52    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl2_2 | ~spl2_4)),
% 0.21/0.52    inference(superposition,[],[f61,f564])).
% 0.21/0.52  fof(f564,plain,(
% 0.21/0.52    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_4)),
% 0.21/0.52    inference(forward_demodulation,[],[f563,f478])).
% 0.21/0.52  fof(f478,plain,(
% 0.21/0.52    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_4)),
% 0.21/0.52    inference(backward_demodulation,[],[f242,f476])).
% 0.21/0.52  fof(f476,plain,(
% 0.21/0.52    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.52    inference(forward_demodulation,[],[f475,f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_2),
% 0.21/0.52    inference(resolution,[],[f112,f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) )),
% 0.21/0.52    inference(resolution,[],[f82,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.52    inference(unused_predicate_definition_removal,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) )),
% 0.21/0.52    inference(forward_demodulation,[],[f60,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_2),
% 0.21/0.52    inference(superposition,[],[f109,f78])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X1),sK1)) )),
% 0.21/0.52    inference(superposition,[],[f67,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X9] : (k7_subset_1(u1_struct_0(sK0),sK1,X9) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X9)))) )),
% 0.21/0.52    inference(resolution,[],[f70,f45])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f64,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f56,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f53,f66])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.52  fof(f475,plain,(
% 0.21/0.52    k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.52    inference(forward_demodulation,[],[f456,f125])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.52    inference(forward_demodulation,[],[f123,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_2),
% 0.21/0.52    inference(superposition,[],[f68,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) | ~spl2_2),
% 0.21/0.52    inference(resolution,[],[f112,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.52    inference(resolution,[],[f69,f63])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f59,f66])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f57,f66])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.52  fof(f456,plain,(
% 0.21/0.52    k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_2),
% 0.21/0.52    inference(resolution,[],[f358,f112])).
% 0.21/0.52  fof(f358,plain,(
% 0.21/0.52    ( ! [X5] : (~r1_tarski(X5,sK1) | k4_subset_1(sK1,X5,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(X5,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))) ) | ~spl2_2),
% 0.21/0.52    inference(resolution,[],[f344,f124])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    r1_tarski(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),sK1) | ~spl2_2),
% 0.21/0.52    inference(superposition,[],[f67,f113])).
% 0.21/0.52  fof(f344,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | ~r1_tarski(X1,X0) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.21/0.52    inference(resolution,[],[f144,f63])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) | ~r1_tarski(X2,X1)) )),
% 0.21/0.52    inference(resolution,[],[f65,f63])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_4),
% 0.21/0.52    inference(resolution,[],[f235,f45])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2))) ) | ~spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f234])).
% 0.21/0.52  fof(f563,plain,(
% 0.21/0.52    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)),
% 0.21/0.52    inference(resolution,[],[f559,f45])).
% 0.21/0.52  fof(f559,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 0.21/0.52    inference(resolution,[],[f49,f44])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    spl2_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f237])).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    $false | spl2_3),
% 0.21/0.52    inference(resolution,[],[f232,f44])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f230])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    ~spl2_3 | spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f152,f234,f230])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ( ! [X2] : (k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f147,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X9) = k2_xboole_0(sK1,X9)) )),
% 0.21/0.52    inference(resolution,[],[f65,f45])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl2_1 | spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f46,f76,f72])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (12825)------------------------------
% 0.21/0.52  % (12825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12825)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (12825)Memory used [KB]: 6652
% 0.21/0.52  % (12825)Time elapsed: 0.096 s
% 0.21/0.52  % (12825)------------------------------
% 0.21/0.52  % (12825)------------------------------
% 0.21/0.52  % (12822)Success in time 0.161 s
%------------------------------------------------------------------------------
