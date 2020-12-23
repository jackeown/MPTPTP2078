%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:24 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 709 expanded)
%              Number of leaves         :   20 ( 207 expanded)
%              Depth                    :   18
%              Number of atoms          :  351 (2894 expanded)
%              Number of equality atoms :   71 ( 874 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f478,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f67,f162,f206,f212,f220,f296,f475,f476])).

fof(f476,plain,
    ( spl2_18
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f369,f217,f203])).

fof(f203,plain,
    ( spl2_18
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f217,plain,
    ( spl2_19
  <=> v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f369,plain,
    ( ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f108,f128])).

fof(f128,plain,(
    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f127,f99])).

fof(f99,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f36,f69])).

fof(f69,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f68,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f68,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f35,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_xboole_0 = k1_tops_1(sK0,X1)
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
          | ~ v2_tops_1(X1,sK0) )
        & ( k1_xboole_0 = k1_tops_1(sK0,X1)
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
        | ~ v2_tops_1(sK1,sK0) )
      & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f127,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f46,f111])).

fof(f111,plain,(
    k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1) ),
    inference(resolution,[],[f99,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f108,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X3,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X3) ) ),
    inference(subsumption_resolution,[],[f103,f35])).

fof(f103,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X3,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X3)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f42,f69])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f475,plain,
    ( spl2_2
    | ~ spl2_11
    | ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | spl2_2
    | ~ spl2_11
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f471,f65])).

fof(f65,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f471,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_11
    | ~ spl2_18 ),
    inference(backward_demodulation,[],[f331,f470])).

fof(f470,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_11
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f196,f205])).

fof(f205,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f203])).

fof(f196,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ spl2_11 ),
    inference(resolution,[],[f165,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f165,plain,
    ( r1_tarski(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ spl2_11 ),
    inference(resolution,[],[f152,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f152,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl2_11
  <=> m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f331,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_11
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f236,f237])).

fof(f237,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f147,f205])).

fof(f147,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f146,f111])).

fof(f146,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f85,f69])).

fof(f85,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f72,f35])).

fof(f72,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f36,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f236,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_11
    | ~ spl2_18 ),
    inference(resolution,[],[f222,f47])).

fof(f222,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_11
    | ~ spl2_18 ),
    inference(backward_demodulation,[],[f152,f205])).

fof(f296,plain,
    ( spl2_1
    | ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl2_1
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f294,f99])).

fof(f294,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_1
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f293,f61])).

fof(f61,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f293,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f290,f234])).

fof(f234,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f233,f128])).

fof(f233,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f232,f69])).

fof(f232,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f226,f35])).

fof(f226,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_18 ),
    inference(trivial_inequality_removal,[],[f225])).

fof(f225,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_18 ),
    inference(superposition,[],[f43,f205])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f290,plain,
    ( ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f107,f111])).

fof(f107,plain,(
    ! [X2] :
      ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X2),sK0)
      | v2_tops_1(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f102,f35])).

fof(f102,plain,(
    ! [X2] :
      ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X2),sK0)
      | v2_tops_1(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f45,f69])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f220,plain,
    ( ~ spl2_1
    | spl2_19 ),
    inference(avatar_split_clause,[],[f215,f217,f59])).

fof(f215,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f214,f111])).

fof(f214,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f213,f69])).

fof(f213,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f70,f35])).

fof(f70,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f36,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f212,plain,
    ( ~ spl2_2
    | ~ spl2_11
    | spl2_17 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_11
    | spl2_17 ),
    inference(subsumption_resolution,[],[f210,f201])).

fof(f201,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | spl2_17 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl2_17
  <=> r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f210,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(trivial_inequality_removal,[],[f209])).

fof(f209,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(superposition,[],[f54,f167])).

fof(f167,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f166,f148])).

fof(f148,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f147,f64])).

fof(f64,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f166,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_11 ),
    inference(resolution,[],[f152,f47])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f206,plain,
    ( ~ spl2_17
    | spl2_18
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f197,f151,f203,f199])).

fof(f197,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_11 ),
    inference(resolution,[],[f165,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f162,plain,(
    spl2_11 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl2_11 ),
    inference(subsumption_resolution,[],[f159,f128])).

fof(f159,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_11 ),
    inference(resolution,[],[f153,f105])).

fof(f105,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f100,f35])).

fof(f100,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f48,f69])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f153,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f67,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f37,f63,f59])).

fof(f37,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f38,f63,f59])).

fof(f38,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (420)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (413)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (430)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.24/0.54  % (431)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.24/0.54  % (414)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.24/0.54  % (409)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.54  % (421)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.24/0.55  % (415)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.24/0.55  % (411)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.24/0.55  % (410)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.24/0.55  % (412)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.24/0.56  % (428)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.55/0.56  % (429)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.55/0.56  % (409)Refutation found. Thanks to Tanya!
% 1.55/0.56  % SZS status Theorem for theBenchmark
% 1.55/0.56  % SZS output start Proof for theBenchmark
% 1.55/0.56  fof(f478,plain,(
% 1.55/0.56    $false),
% 1.55/0.56    inference(avatar_sat_refutation,[],[f66,f67,f162,f206,f212,f220,f296,f475,f476])).
% 1.55/0.56  fof(f476,plain,(
% 1.55/0.56    spl2_18 | ~spl2_19),
% 1.55/0.56    inference(avatar_split_clause,[],[f369,f217,f203])).
% 1.55/0.56  fof(f203,plain,(
% 1.55/0.56    spl2_18 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.55/0.56  fof(f217,plain,(
% 1.55/0.56    spl2_19 <=> v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 1.55/0.56  fof(f369,plain,(
% 1.55/0.56    ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))),
% 1.55/0.56    inference(resolution,[],[f108,f128])).
% 1.55/0.56  fof(f128,plain,(
% 1.55/0.56    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.55/0.56    inference(subsumption_resolution,[],[f127,f99])).
% 1.55/0.56  fof(f99,plain,(
% 1.55/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.55/0.56    inference(backward_demodulation,[],[f36,f69])).
% 1.55/0.56  fof(f69,plain,(
% 1.55/0.56    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.55/0.56    inference(resolution,[],[f68,f39])).
% 1.55/0.56  fof(f39,plain,(
% 1.55/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f15])).
% 1.55/0.56  fof(f15,plain,(
% 1.55/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f6])).
% 1.55/0.56  fof(f6,axiom,(
% 1.55/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.55/0.56  fof(f68,plain,(
% 1.55/0.56    l1_struct_0(sK0)),
% 1.55/0.56    inference(resolution,[],[f35,f40])).
% 1.55/0.56  fof(f40,plain,(
% 1.55/0.56    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f16])).
% 1.55/0.56  fof(f16,plain,(
% 1.55/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f8])).
% 1.55/0.56  fof(f8,axiom,(
% 1.55/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.55/0.56  fof(f35,plain,(
% 1.55/0.56    l1_pre_topc(sK0)),
% 1.55/0.56    inference(cnf_transformation,[],[f28])).
% 1.55/0.56  fof(f28,plain,(
% 1.55/0.56    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.55/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).
% 1.55/0.56  fof(f26,plain,(
% 1.55/0.56    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.55/0.56    introduced(choice_axiom,[])).
% 1.55/0.56  fof(f27,plain,(
% 1.55/0.56    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.55/0.56    introduced(choice_axiom,[])).
% 1.55/0.56  fof(f25,plain,(
% 1.55/0.56    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.55/0.56    inference(flattening,[],[f24])).
% 1.55/0.56  fof(f24,plain,(
% 1.55/0.56    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.55/0.56    inference(nnf_transformation,[],[f14])).
% 1.55/0.56  fof(f14,plain,(
% 1.55/0.56    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f13])).
% 1.55/0.56  fof(f13,negated_conjecture,(
% 1.55/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.55/0.56    inference(negated_conjecture,[],[f12])).
% 1.55/0.56  fof(f12,conjecture,(
% 1.55/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 1.55/0.56  fof(f36,plain,(
% 1.55/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.56    inference(cnf_transformation,[],[f28])).
% 1.55/0.56  fof(f127,plain,(
% 1.55/0.56    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.55/0.56    inference(superposition,[],[f46,f111])).
% 1.55/0.56  fof(f111,plain,(
% 1.55/0.56    k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1)),
% 1.55/0.56    inference(resolution,[],[f99,f47])).
% 1.55/0.56  fof(f47,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f21])).
% 1.55/0.56  fof(f21,plain,(
% 1.55/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.56    inference(ennf_transformation,[],[f3])).
% 1.55/0.56  fof(f3,axiom,(
% 1.55/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.55/0.56  fof(f46,plain,(
% 1.55/0.56    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.55/0.56    inference(cnf_transformation,[],[f20])).
% 1.55/0.56  fof(f20,plain,(
% 1.55/0.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.56    inference(ennf_transformation,[],[f4])).
% 1.55/0.56  fof(f4,axiom,(
% 1.55/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.55/0.56  fof(f108,plain,(
% 1.55/0.56    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X3,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X3)) )),
% 1.55/0.56    inference(subsumption_resolution,[],[f103,f35])).
% 1.55/0.56  fof(f103,plain,(
% 1.55/0.56    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X3,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X3) | ~l1_pre_topc(sK0)) )),
% 1.55/0.56    inference(superposition,[],[f42,f69])).
% 1.55/0.56  fof(f42,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f29])).
% 1.55/0.56  fof(f29,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(nnf_transformation,[],[f18])).
% 1.55/0.56  fof(f18,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f10])).
% 1.55/0.56  fof(f10,axiom,(
% 1.55/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 1.55/0.56  fof(f475,plain,(
% 1.55/0.56    spl2_2 | ~spl2_11 | ~spl2_18),
% 1.55/0.56    inference(avatar_contradiction_clause,[],[f474])).
% 1.55/0.56  fof(f474,plain,(
% 1.55/0.56    $false | (spl2_2 | ~spl2_11 | ~spl2_18)),
% 1.55/0.56    inference(subsumption_resolution,[],[f471,f65])).
% 1.55/0.56  fof(f65,plain,(
% 1.55/0.56    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl2_2),
% 1.55/0.56    inference(avatar_component_clause,[],[f63])).
% 1.55/0.56  fof(f63,plain,(
% 1.55/0.56    spl2_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.55/0.56  fof(f471,plain,(
% 1.55/0.56    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl2_11 | ~spl2_18)),
% 1.55/0.56    inference(backward_demodulation,[],[f331,f470])).
% 1.55/0.56  fof(f470,plain,(
% 1.55/0.56    k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl2_11 | ~spl2_18)),
% 1.55/0.56    inference(forward_demodulation,[],[f196,f205])).
% 1.55/0.56  fof(f205,plain,(
% 1.55/0.56    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_18),
% 1.55/0.56    inference(avatar_component_clause,[],[f203])).
% 1.55/0.56  fof(f196,plain,(
% 1.55/0.56    k1_xboole_0 = k4_xboole_0(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) | ~spl2_11),
% 1.55/0.56    inference(resolution,[],[f165,f55])).
% 1.55/0.56  fof(f55,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.55/0.56    inference(cnf_transformation,[],[f34])).
% 1.55/0.56  fof(f34,plain,(
% 1.55/0.56    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.55/0.56    inference(nnf_transformation,[],[f2])).
% 1.55/0.56  fof(f2,axiom,(
% 1.55/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.55/0.56  fof(f165,plain,(
% 1.55/0.56    r1_tarski(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) | ~spl2_11),
% 1.55/0.56    inference(resolution,[],[f152,f52])).
% 1.55/0.56  fof(f52,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f33])).
% 1.55/0.56  fof(f33,plain,(
% 1.55/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.55/0.56    inference(nnf_transformation,[],[f5])).
% 1.55/0.56  fof(f5,axiom,(
% 1.55/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.55/0.56  fof(f152,plain,(
% 1.55/0.56    m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_11),
% 1.55/0.56    inference(avatar_component_clause,[],[f151])).
% 1.55/0.56  fof(f151,plain,(
% 1.55/0.56    spl2_11 <=> m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.55/0.56  fof(f331,plain,(
% 1.55/0.56    k1_tops_1(sK0,sK1) = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl2_11 | ~spl2_18)),
% 1.55/0.56    inference(forward_demodulation,[],[f236,f237])).
% 1.55/0.56  fof(f237,plain,(
% 1.55/0.56    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl2_18),
% 1.55/0.56    inference(forward_demodulation,[],[f147,f205])).
% 1.55/0.56  fof(f147,plain,(
% 1.55/0.56    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))),
% 1.55/0.56    inference(forward_demodulation,[],[f146,f111])).
% 1.55/0.56  fof(f146,plain,(
% 1.55/0.56    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 1.55/0.56    inference(forward_demodulation,[],[f85,f69])).
% 1.55/0.56  fof(f85,plain,(
% 1.55/0.56    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 1.55/0.56    inference(subsumption_resolution,[],[f72,f35])).
% 1.55/0.56  fof(f72,plain,(
% 1.55/0.56    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0)),
% 1.55/0.56    inference(resolution,[],[f36,f41])).
% 1.55/0.56  fof(f41,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f17])).
% 1.55/0.56  fof(f17,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f9])).
% 1.55/0.56  fof(f9,axiom,(
% 1.55/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 1.55/0.56  fof(f236,plain,(
% 1.55/0.56    k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl2_11 | ~spl2_18)),
% 1.55/0.56    inference(resolution,[],[f222,f47])).
% 1.55/0.56  fof(f222,plain,(
% 1.55/0.56    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_11 | ~spl2_18)),
% 1.55/0.56    inference(backward_demodulation,[],[f152,f205])).
% 1.55/0.56  fof(f296,plain,(
% 1.55/0.56    spl2_1 | ~spl2_18),
% 1.55/0.56    inference(avatar_contradiction_clause,[],[f295])).
% 1.55/0.56  fof(f295,plain,(
% 1.55/0.56    $false | (spl2_1 | ~spl2_18)),
% 1.55/0.56    inference(subsumption_resolution,[],[f294,f99])).
% 1.55/0.56  fof(f294,plain,(
% 1.55/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (spl2_1 | ~spl2_18)),
% 1.55/0.56    inference(subsumption_resolution,[],[f293,f61])).
% 1.55/0.56  fof(f61,plain,(
% 1.55/0.56    ~v2_tops_1(sK1,sK0) | spl2_1),
% 1.55/0.56    inference(avatar_component_clause,[],[f59])).
% 1.55/0.56  fof(f59,plain,(
% 1.55/0.56    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.55/0.56  fof(f293,plain,(
% 1.55/0.56    v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_18),
% 1.55/0.56    inference(subsumption_resolution,[],[f290,f234])).
% 1.55/0.56  fof(f234,plain,(
% 1.55/0.56    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~spl2_18),
% 1.55/0.56    inference(subsumption_resolution,[],[f233,f128])).
% 1.55/0.56  fof(f233,plain,(
% 1.55/0.56    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~spl2_18),
% 1.55/0.56    inference(forward_demodulation,[],[f232,f69])).
% 1.55/0.56  fof(f232,plain,(
% 1.55/0.56    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_18),
% 1.55/0.56    inference(subsumption_resolution,[],[f226,f35])).
% 1.55/0.56  fof(f226,plain,(
% 1.55/0.56    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_18),
% 1.55/0.56    inference(trivial_inequality_removal,[],[f225])).
% 1.55/0.56  fof(f225,plain,(
% 1.55/0.56    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_18),
% 1.55/0.56    inference(superposition,[],[f43,f205])).
% 1.55/0.56  fof(f43,plain,(
% 1.55/0.56    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f29])).
% 1.55/0.56  fof(f290,plain,(
% 1.55/0.56    ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.55/0.56    inference(superposition,[],[f107,f111])).
% 1.55/0.56  fof(f107,plain,(
% 1.55/0.56    ( ! [X2] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X2),sK0) | v2_tops_1(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.55/0.56    inference(subsumption_resolution,[],[f102,f35])).
% 1.55/0.56  fof(f102,plain,(
% 1.55/0.56    ( ! [X2] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X2),sK0) | v2_tops_1(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.55/0.56    inference(superposition,[],[f45,f69])).
% 1.55/0.56  fof(f45,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f30])).
% 1.55/0.56  fof(f30,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(nnf_transformation,[],[f19])).
% 1.55/0.56  fof(f19,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f11])).
% 1.55/0.56  fof(f11,axiom,(
% 1.55/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).
% 1.55/0.56  fof(f220,plain,(
% 1.55/0.56    ~spl2_1 | spl2_19),
% 1.55/0.56    inference(avatar_split_clause,[],[f215,f217,f59])).
% 1.55/0.56  fof(f215,plain,(
% 1.55/0.56    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~v2_tops_1(sK1,sK0)),
% 1.55/0.56    inference(forward_demodulation,[],[f214,f111])).
% 1.55/0.56  fof(f214,plain,(
% 1.55/0.56    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~v2_tops_1(sK1,sK0)),
% 1.55/0.56    inference(forward_demodulation,[],[f213,f69])).
% 1.55/0.56  fof(f213,plain,(
% 1.55/0.56    ~v2_tops_1(sK1,sK0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.55/0.56    inference(subsumption_resolution,[],[f70,f35])).
% 1.55/0.56  fof(f70,plain,(
% 1.55/0.56    ~v2_tops_1(sK1,sK0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0)),
% 1.55/0.56    inference(resolution,[],[f36,f44])).
% 1.55/0.56  fof(f44,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f30])).
% 1.55/0.56  fof(f212,plain,(
% 1.55/0.56    ~spl2_2 | ~spl2_11 | spl2_17),
% 1.55/0.56    inference(avatar_contradiction_clause,[],[f211])).
% 1.55/0.56  fof(f211,plain,(
% 1.55/0.56    $false | (~spl2_2 | ~spl2_11 | spl2_17)),
% 1.55/0.56    inference(subsumption_resolution,[],[f210,f201])).
% 1.55/0.56  fof(f201,plain,(
% 1.55/0.56    ~r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | spl2_17),
% 1.55/0.56    inference(avatar_component_clause,[],[f199])).
% 1.55/0.56  fof(f199,plain,(
% 1.55/0.56    spl2_17 <=> r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.55/0.56  fof(f210,plain,(
% 1.55/0.56    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_11)),
% 1.55/0.56    inference(trivial_inequality_removal,[],[f209])).
% 1.55/0.56  fof(f209,plain,(
% 1.55/0.56    k1_xboole_0 != k1_xboole_0 | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_11)),
% 1.55/0.56    inference(superposition,[],[f54,f167])).
% 1.55/0.56  fof(f167,plain,(
% 1.55/0.56    k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_11)),
% 1.55/0.56    inference(forward_demodulation,[],[f166,f148])).
% 1.55/0.56  fof(f148,plain,(
% 1.55/0.56    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | ~spl2_2),
% 1.55/0.56    inference(forward_demodulation,[],[f147,f64])).
% 1.55/0.56  fof(f64,plain,(
% 1.55/0.56    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 1.55/0.56    inference(avatar_component_clause,[],[f63])).
% 1.55/0.56  fof(f166,plain,(
% 1.55/0.56    k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | ~spl2_11),
% 1.55/0.56    inference(resolution,[],[f152,f47])).
% 1.55/0.56  fof(f54,plain,(
% 1.55/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f34])).
% 1.55/0.56  fof(f206,plain,(
% 1.55/0.56    ~spl2_17 | spl2_18 | ~spl2_11),
% 1.55/0.56    inference(avatar_split_clause,[],[f197,f151,f203,f199])).
% 1.55/0.56  fof(f197,plain,(
% 1.55/0.56    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | ~spl2_11),
% 1.55/0.56    inference(resolution,[],[f165,f51])).
% 1.55/0.56  fof(f51,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f32])).
% 1.55/0.56  fof(f32,plain,(
% 1.55/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.55/0.56    inference(flattening,[],[f31])).
% 1.55/0.57  fof(f31,plain,(
% 1.55/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.55/0.57    inference(nnf_transformation,[],[f1])).
% 1.55/0.57  fof(f1,axiom,(
% 1.55/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.55/0.57  fof(f162,plain,(
% 1.55/0.57    spl2_11),
% 1.55/0.57    inference(avatar_contradiction_clause,[],[f161])).
% 1.55/0.57  fof(f161,plain,(
% 1.55/0.57    $false | spl2_11),
% 1.55/0.57    inference(subsumption_resolution,[],[f159,f128])).
% 1.55/0.57  fof(f159,plain,(
% 1.55/0.57    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl2_11),
% 1.55/0.57    inference(resolution,[],[f153,f105])).
% 1.55/0.57  fof(f105,plain,(
% 1.55/0.57    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.55/0.57    inference(subsumption_resolution,[],[f100,f35])).
% 1.55/0.57  fof(f100,plain,(
% 1.55/0.57    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.55/0.57    inference(superposition,[],[f48,f69])).
% 1.55/0.57  fof(f48,plain,(
% 1.55/0.57    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f23])).
% 1.55/0.57  fof(f23,plain,(
% 1.55/0.57    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.55/0.57    inference(flattening,[],[f22])).
% 1.55/0.57  fof(f22,plain,(
% 1.55/0.57    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.55/0.57    inference(ennf_transformation,[],[f7])).
% 1.55/0.57  fof(f7,axiom,(
% 1.55/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.55/0.57  fof(f153,plain,(
% 1.55/0.57    ~m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | spl2_11),
% 1.55/0.57    inference(avatar_component_clause,[],[f151])).
% 1.55/0.57  fof(f67,plain,(
% 1.55/0.57    spl2_1 | spl2_2),
% 1.55/0.57    inference(avatar_split_clause,[],[f37,f63,f59])).
% 1.55/0.57  fof(f37,plain,(
% 1.55/0.57    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 1.55/0.57    inference(cnf_transformation,[],[f28])).
% 1.55/0.57  fof(f66,plain,(
% 1.55/0.57    ~spl2_1 | ~spl2_2),
% 1.55/0.57    inference(avatar_split_clause,[],[f38,f63,f59])).
% 1.55/0.57  fof(f38,plain,(
% 1.55/0.57    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 1.55/0.57    inference(cnf_transformation,[],[f28])).
% 1.55/0.57  % SZS output end Proof for theBenchmark
% 1.55/0.57  % (409)------------------------------
% 1.55/0.57  % (409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (409)Termination reason: Refutation
% 1.55/0.57  
% 1.55/0.57  % (409)Memory used [KB]: 10874
% 1.55/0.57  % (409)Time elapsed: 0.114 s
% 1.55/0.57  % (409)------------------------------
% 1.55/0.57  % (409)------------------------------
% 1.55/0.57  % (407)Success in time 0.211 s
%------------------------------------------------------------------------------
