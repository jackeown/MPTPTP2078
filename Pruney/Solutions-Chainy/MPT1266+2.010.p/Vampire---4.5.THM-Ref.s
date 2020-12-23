%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  131 (1318 expanded)
%              Number of leaves         :   20 ( 373 expanded)
%              Depth                    :   23
%              Number of atoms          :  363 (5420 expanded)
%              Number of equality atoms :   79 (1670 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f631,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f216,f491,f516,f608,f630])).

fof(f630,plain,
    ( ~ spl2_1
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f629])).

fof(f629,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f628,f613])).

fof(f613,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f42,f69])).

fof(f69,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f42,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
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

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f628,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_11 ),
    inference(backward_demodulation,[],[f522,f627])).

fof(f627,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f620,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f60,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f620,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_11 ),
    inference(resolution,[],[f612,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f612,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f611,f86])).

fof(f86,plain,(
    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f85,f65])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f40,f64])).

fof(f64,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f44,f63])).

fof(f63,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f45,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f51,f83])).

fof(f83,plain,(
    k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1) ),
    inference(resolution,[],[f52,f65])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f611,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f607,f64])).

fof(f607,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f606,f64])).

fof(f606,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f604,f39])).

fof(f604,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_11 ),
    inference(superposition,[],[f54,f211])).

fof(f211,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl2_11
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f522,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_11 ),
    inference(backward_demodulation,[],[f495,f521])).

fof(f521,plain,
    ( k2_struct_0(sK0) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_11 ),
    inference(backward_demodulation,[],[f494,f211])).

fof(f494,plain,(
    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f239,f463])).

fof(f463,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f428,f83])).

% (26090)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f428,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f346,f65])).

fof(f346,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) ) ),
    inference(subsumption_resolution,[],[f343,f39])).

fof(f343,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f46,f64])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f239,plain,(
    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) ),
    inference(resolution,[],[f109,f86])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) ) ),
    inference(resolution,[],[f108,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f108,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f107,f39])).

fof(f107,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f54,f64])).

fof(f495,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f463,f494])).

fof(f608,plain,
    ( spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f520,f213,f67])).

fof(f213,plain,
    ( spl2_12
  <=> v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f520,plain,
    ( ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f237,f65])).

fof(f237,plain,
    ( ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f232,f83])).

fof(f232,plain,(
    ! [X0] :
      ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f230,f39])).

fof(f230,plain,(
    ! [X0] :
      ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f50,f64])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f516,plain,
    ( ~ spl2_1
    | spl2_12 ),
    inference(avatar_contradiction_clause,[],[f515])).

fof(f515,plain,
    ( $false
    | ~ spl2_1
    | spl2_12 ),
    inference(subsumption_resolution,[],[f69,f514])).

fof(f514,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_12 ),
    inference(subsumption_resolution,[],[f513,f65])).

fof(f513,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_12 ),
    inference(subsumption_resolution,[],[f222,f215])).

fof(f215,plain,
    ( ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | spl2_12 ),
    inference(avatar_component_clause,[],[f213])).

fof(f222,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f218,f83])).

fof(f218,plain,(
    ! [X0] :
      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | ~ v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f217,f39])).

fof(f217,plain,(
    ! [X0] :
      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | ~ v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f49,f64])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f491,plain,
    ( ~ spl2_2
    | spl2_12 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | ~ spl2_2
    | spl2_12 ),
    inference(subsumption_resolution,[],[f489,f86])).

fof(f489,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_2
    | spl2_12 ),
    inference(forward_demodulation,[],[f488,f64])).

fof(f488,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | spl2_12 ),
    inference(subsumption_resolution,[],[f487,f39])).

fof(f487,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | spl2_12 ),
    inference(subsumption_resolution,[],[f486,f215])).

fof(f486,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f484])).

fof(f484,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f48,f466])).

fof(f466,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f465,f122])).

fof(f122,plain,
    ( k2_struct_0(sK0) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f121,f43])).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f121,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl2_2 ),
    inference(resolution,[],[f118,f52])).

fof(f118,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f117,f65])).

fof(f117,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f116,f64])).

fof(f116,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f115,f64])).

fof(f115,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f113,f39])).

fof(f113,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f55,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f465,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f239,f464])).

fof(f464,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f463,f73])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f216,plain,
    ( spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f174,f213,f209])).

fof(f174,plain,
    ( ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f173,f86])).

fof(f173,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f170,f39])).

fof(f170,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f47,f64])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f41,f71,f67])).

fof(f41,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:39:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (26095)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.47  % (26103)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.48  % (26085)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (26092)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (26083)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (26086)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (26103)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (26100)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f631,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f74,f216,f491,f516,f608,f630])).
% 0.21/0.50  fof(f630,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_11),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f629])).
% 0.21/0.50  fof(f629,plain,(
% 0.21/0.50    $false | (~spl2_1 | ~spl2_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f628,f613])).
% 0.21/0.50  fof(f613,plain,(
% 0.21/0.50    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~spl2_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f42,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    v2_tops_1(sK1,sK0) | ~spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.21/0.50  fof(f628,plain,(
% 0.21/0.50    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_11),
% 0.21/0.50    inference(backward_demodulation,[],[f522,f627])).
% 0.21/0.50  fof(f627,plain,(
% 0.21/0.50    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl2_11),
% 0.21/0.50    inference(forward_demodulation,[],[f620,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(resolution,[],[f60,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.50  fof(f620,plain,(
% 0.21/0.50    k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl2_11),
% 0.21/0.50    inference(resolution,[],[f612,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.50  fof(f612,plain,(
% 0.21/0.50    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_11),
% 0.21/0.50    inference(subsumption_resolution,[],[f611,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f85,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f40,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f44,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    l1_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f45,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(superposition,[],[f51,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1)),
% 0.21/0.50    inference(resolution,[],[f52,f65])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.50  fof(f611,plain,(
% 0.21/0.50    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_11),
% 0.21/0.50    inference(forward_demodulation,[],[f607,f64])).
% 0.21/0.50  fof(f607,plain,(
% 0.21/0.50    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_11),
% 0.21/0.50    inference(forward_demodulation,[],[f606,f64])).
% 0.21/0.50  fof(f606,plain,(
% 0.21/0.50    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_11),
% 0.21/0.50    inference(subsumption_resolution,[],[f604,f39])).
% 0.21/0.50  fof(f604,plain,(
% 0.21/0.50    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_11),
% 0.21/0.50    inference(superposition,[],[f54,f211])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f209])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    spl2_11 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.51  fof(f522,plain,(
% 0.21/0.51    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl2_11),
% 0.21/0.51    inference(backward_demodulation,[],[f495,f521])).
% 0.21/0.51  fof(f521,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl2_11),
% 0.21/0.51    inference(backward_demodulation,[],[f494,f211])).
% 0.21/0.51  fof(f494,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 0.21/0.51    inference(backward_demodulation,[],[f239,f463])).
% 0.21/0.51  fof(f463,plain,(
% 0.21/0.51    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))),
% 0.21/0.51    inference(forward_demodulation,[],[f428,f83])).
% 0.21/0.51  % (26090)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  fof(f428,plain,(
% 0.21/0.51    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 0.21/0.51    inference(resolution,[],[f346,f65])).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f343,f39])).
% 0.21/0.51  fof(f343,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.51    inference(superposition,[],[f46,f64])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))))),
% 0.21/0.51    inference(resolution,[],[f109,f86])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0)))) )),
% 0.21/0.51    inference(resolution,[],[f108,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f107,f39])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.51    inference(superposition,[],[f54,f64])).
% 0.21/0.51  fof(f495,plain,(
% 0.21/0.51    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 0.21/0.51    inference(backward_demodulation,[],[f463,f494])).
% 0.21/0.51  fof(f608,plain,(
% 0.21/0.51    spl2_1 | ~spl2_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f520,f213,f67])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    spl2_12 <=> v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.51  fof(f520,plain,(
% 0.21/0.51    ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | v2_tops_1(sK1,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f237,f65])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.51    inference(superposition,[],[f232,f83])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f230,f39])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.51    inference(superposition,[],[f50,f64])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 0.21/0.51  fof(f516,plain,(
% 0.21/0.51    ~spl2_1 | spl2_12),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f515])).
% 0.21/0.51  fof(f515,plain,(
% 0.21/0.51    $false | (~spl2_1 | spl2_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f69,f514])).
% 0.21/0.51  fof(f514,plain,(
% 0.21/0.51    ~v2_tops_1(sK1,sK0) | spl2_12),
% 0.21/0.51    inference(subsumption_resolution,[],[f513,f65])).
% 0.21/0.51  fof(f513,plain,(
% 0.21/0.51    ~v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl2_12),
% 0.21/0.51    inference(subsumption_resolution,[],[f222,f215])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | spl2_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f213])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.51    inference(superposition,[],[f218,f83])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    ( ! [X0] : (v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f217,f39])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    ( ! [X0] : (v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.51    inference(superposition,[],[f49,f64])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f491,plain,(
% 0.21/0.51    ~spl2_2 | spl2_12),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f490])).
% 0.21/0.51  fof(f490,plain,(
% 0.21/0.51    $false | (~spl2_2 | spl2_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f489,f86])).
% 0.21/0.51  fof(f489,plain,(
% 0.21/0.51    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_2 | spl2_12)),
% 0.21/0.51    inference(forward_demodulation,[],[f488,f64])).
% 0.21/0.51  fof(f488,plain,(
% 0.21/0.51    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | spl2_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f487,f39])).
% 0.21/0.51  fof(f487,plain,(
% 0.21/0.51    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_2 | spl2_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f486,f215])).
% 0.21/0.51  fof(f486,plain,(
% 0.21/0.51    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f484])).
% 0.21/0.51  fof(f484,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.51    inference(superposition,[],[f48,f466])).
% 0.21/0.51  fof(f466,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_2),
% 0.21/0.51    inference(forward_demodulation,[],[f465,f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) | ~spl2_2),
% 0.21/0.51    inference(forward_demodulation,[],[f121,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) | ~spl2_2),
% 0.21/0.51    inference(resolution,[],[f118,f52])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f117,f65])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_2),
% 0.21/0.51    inference(forward_demodulation,[],[f116,f64])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.21/0.51    inference(forward_demodulation,[],[f115,f64])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f113,f39])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.51    inference(superposition,[],[f55,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl2_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.21/0.51  fof(f465,plain,(
% 0.21/0.51    k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_2),
% 0.21/0.51    inference(backward_demodulation,[],[f239,f464])).
% 0.21/0.51  fof(f464,plain,(
% 0.21/0.51    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | ~spl2_2),
% 0.21/0.51    inference(forward_demodulation,[],[f463,f73])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    spl2_11 | ~spl2_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f174,f213,f209])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(resolution,[],[f173,f86])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f170,f39])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.51    inference(superposition,[],[f47,f64])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl2_1 | spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f71,f67])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (26103)------------------------------
% 0.21/0.51  % (26103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26103)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (26103)Memory used [KB]: 11001
% 0.21/0.51  % (26103)Time elapsed: 0.085 s
% 0.21/0.51  % (26103)------------------------------
% 0.21/0.51  % (26103)------------------------------
% 0.21/0.51  % (26081)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (26082)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (26077)Success in time 0.152 s
%------------------------------------------------------------------------------
