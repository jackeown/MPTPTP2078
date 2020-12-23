%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:21 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 170 expanded)
%              Number of leaves         :   13 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  167 ( 610 expanded)
%              Number of equality atoms :   41 ( 163 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f247,f255,f266])).

fof(f266,plain,(
    ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f259,f52])).

fof(f52,plain,(
    k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_pre_topc(sK0,X1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X1)))
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( k2_pre_topc(sK0,X1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X1)))
        & v3_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).

fof(f259,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f81,f254])).

fof(f254,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl3_24
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f81,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f49,f50,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tops_1)).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f255,plain,
    ( spl3_24
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f250,f139,f252])).

fof(f139,plain,
    ( spl3_8
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f250,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(global_subsumption,[],[f148,f249])).

fof(f249,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f248,f86])).

fof(f86,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f84,f85])).

fof(f85,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f50,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f84,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f50,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f248,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f163,f49])).

fof(f163,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f87,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
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

fof(f87,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f82,f85])).

fof(f82,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f49,f50,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f148,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f147,f49])).

fof(f147,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f125,f51])).

fof(f51,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f125,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f58,f86])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f247,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl3_8 ),
    inference(subsumption_resolution,[],[f242,f59])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f242,plain,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f141,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f141,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (13424)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.48  % (13432)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (13437)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (13417)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (13417)Refutation not found, incomplete strategy% (13417)------------------------------
% 0.21/0.50  % (13417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13427)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (13419)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (13427)Refutation not found, incomplete strategy% (13427)------------------------------
% 0.21/0.51  % (13427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13427)Memory used [KB]: 10618
% 0.21/0.51  % (13427)Time elapsed: 0.096 s
% 0.21/0.51  % (13427)------------------------------
% 0.21/0.51  % (13427)------------------------------
% 0.21/0.51  % (13429)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (13439)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (13421)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (13431)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (13417)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13417)Memory used [KB]: 1791
% 0.21/0.51  % (13417)Time elapsed: 0.096 s
% 0.21/0.51  % (13417)------------------------------
% 0.21/0.51  % (13417)------------------------------
% 0.21/0.52  % (13421)Refutation not found, incomplete strategy% (13421)------------------------------
% 0.21/0.52  % (13421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13421)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13421)Memory used [KB]: 6268
% 0.21/0.52  % (13421)Time elapsed: 0.110 s
% 0.21/0.52  % (13421)------------------------------
% 0.21/0.52  % (13421)------------------------------
% 0.21/0.52  % (13426)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (13426)Refutation not found, incomplete strategy% (13426)------------------------------
% 0.21/0.52  % (13426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13426)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13426)Memory used [KB]: 10746
% 0.21/0.52  % (13426)Time elapsed: 0.105 s
% 0.21/0.52  % (13426)------------------------------
% 0.21/0.52  % (13426)------------------------------
% 0.21/0.52  % (13445)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (13444)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (13423)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (13440)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (13438)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (13418)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.43/0.54  % (13420)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.43/0.54  % (13443)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.54  % (13446)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.54  % (13443)Refutation found. Thanks to Tanya!
% 1.43/0.54  % SZS status Theorem for theBenchmark
% 1.43/0.54  % SZS output start Proof for theBenchmark
% 1.43/0.54  fof(f267,plain,(
% 1.43/0.54    $false),
% 1.43/0.54    inference(avatar_sat_refutation,[],[f247,f255,f266])).
% 1.43/0.54  fof(f266,plain,(
% 1.43/0.54    ~spl3_24),
% 1.43/0.54    inference(avatar_contradiction_clause,[],[f265])).
% 1.43/0.54  fof(f265,plain,(
% 1.43/0.54    $false | ~spl3_24),
% 1.43/0.54    inference(subsumption_resolution,[],[f259,f52])).
% 1.43/0.54  fof(f52,plain,(
% 1.43/0.54    k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 1.43/0.54    inference(cnf_transformation,[],[f41])).
% 1.43/0.54  fof(f41,plain,(
% 1.43/0.54    (k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.43/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f40,f39])).
% 1.43/0.54  fof(f39,plain,(
% 1.43/0.54    ? [X0] : (? [X1] : (k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (k2_pre_topc(sK0,X1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X1))) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.43/0.54    introduced(choice_axiom,[])).
% 1.43/0.54  fof(f40,plain,(
% 1.43/0.54    ? [X1] : (k2_pre_topc(sK0,X1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X1))) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.43/0.54    introduced(choice_axiom,[])).
% 1.43/0.54  fof(f25,plain,(
% 1.43/0.54    ? [X0] : (? [X1] : (k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.43/0.54    inference(flattening,[],[f24])).
% 1.43/0.54  fof(f24,plain,(
% 1.43/0.54    ? [X0] : (? [X1] : ((k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) & v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.43/0.54    inference(ennf_transformation,[],[f22])).
% 1.43/0.54  fof(f22,negated_conjecture,(
% 1.43/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 1.43/0.54    inference(negated_conjecture,[],[f21])).
% 1.43/0.54  fof(f21,conjecture,(
% 1.43/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).
% 1.43/0.54  fof(f259,plain,(
% 1.43/0.54    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~spl3_24),
% 1.43/0.54    inference(backward_demodulation,[],[f81,f254])).
% 1.43/0.54  fof(f254,plain,(
% 1.43/0.54    sK1 = k1_tops_1(sK0,sK1) | ~spl3_24),
% 1.43/0.54    inference(avatar_component_clause,[],[f252])).
% 1.43/0.54  fof(f252,plain,(
% 1.43/0.54    spl3_24 <=> sK1 = k1_tops_1(sK0,sK1)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.43/0.54  fof(f81,plain,(
% 1.43/0.54    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f49,f50,f55])).
% 1.43/0.54  fof(f55,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f27])).
% 1.43/0.54  fof(f27,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.54    inference(ennf_transformation,[],[f20])).
% 1.43/0.54  fof(f20,axiom,(
% 1.43/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tops_1)).
% 1.43/0.54  fof(f50,plain,(
% 1.43/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.43/0.54    inference(cnf_transformation,[],[f41])).
% 1.43/0.54  fof(f49,plain,(
% 1.43/0.54    l1_pre_topc(sK0)),
% 1.43/0.54    inference(cnf_transformation,[],[f41])).
% 1.43/0.54  fof(f255,plain,(
% 1.43/0.54    spl3_24 | ~spl3_8),
% 1.43/0.54    inference(avatar_split_clause,[],[f250,f139,f252])).
% 1.43/0.54  fof(f139,plain,(
% 1.43/0.54    spl3_8 <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.43/0.54  fof(f250,plain,(
% 1.43/0.54    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k1_tops_1(sK0,sK1)),
% 1.43/0.54    inference(global_subsumption,[],[f148,f249])).
% 1.43/0.54  fof(f249,plain,(
% 1.43/0.54    sK1 = k1_tops_1(sK0,sK1) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.43/0.54    inference(forward_demodulation,[],[f248,f86])).
% 1.43/0.54  fof(f86,plain,(
% 1.43/0.54    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.43/0.54    inference(forward_demodulation,[],[f84,f85])).
% 1.43/0.54  fof(f85,plain,(
% 1.43/0.54    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f50,f66])).
% 1.43/0.54  fof(f66,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.43/0.54    inference(cnf_transformation,[],[f32])).
% 1.43/0.54  fof(f32,plain,(
% 1.43/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.54    inference(ennf_transformation,[],[f12])).
% 1.43/0.54  fof(f12,axiom,(
% 1.43/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.43/0.54  fof(f84,plain,(
% 1.43/0.54    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f50,f67])).
% 1.43/0.54  fof(f67,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.43/0.54    inference(cnf_transformation,[],[f33])).
% 1.43/0.54  fof(f33,plain,(
% 1.43/0.54    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.54    inference(ennf_transformation,[],[f13])).
% 1.43/0.54  fof(f13,axiom,(
% 1.43/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.43/0.54  fof(f248,plain,(
% 1.43/0.54    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.43/0.54    inference(subsumption_resolution,[],[f163,f49])).
% 1.43/0.54  fof(f163,plain,(
% 1.43/0.54    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.43/0.54    inference(superposition,[],[f87,f56])).
% 1.43/0.54  fof(f56,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f29])).
% 1.43/0.54  fof(f29,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.54    inference(flattening,[],[f28])).
% 1.43/0.54  fof(f28,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.54    inference(ennf_transformation,[],[f23])).
% 1.43/0.54  fof(f23,plain,(
% 1.43/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 1.43/0.54    inference(pure_predicate_removal,[],[f17])).
% 1.43/0.54  fof(f17,axiom,(
% 1.43/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.43/0.54  fof(f87,plain,(
% 1.43/0.54    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 1.43/0.54    inference(forward_demodulation,[],[f82,f85])).
% 1.43/0.54  fof(f82,plain,(
% 1.43/0.54    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f49,f50,f54])).
% 1.43/0.54  fof(f54,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f26])).
% 1.43/0.54  fof(f26,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.54    inference(ennf_transformation,[],[f18])).
% 1.43/0.54  fof(f18,axiom,(
% 1.43/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 1.43/0.54  fof(f148,plain,(
% 1.43/0.54    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.43/0.54    inference(subsumption_resolution,[],[f147,f49])).
% 1.43/0.54  fof(f147,plain,(
% 1.43/0.54    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.43/0.54    inference(subsumption_resolution,[],[f125,f51])).
% 1.43/0.54  fof(f51,plain,(
% 1.43/0.54    v3_pre_topc(sK1,sK0)),
% 1.43/0.54    inference(cnf_transformation,[],[f41])).
% 1.43/0.54  fof(f125,plain,(
% 1.43/0.54    ~v3_pre_topc(sK1,sK0) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.43/0.54    inference(superposition,[],[f58,f86])).
% 1.43/0.54  fof(f58,plain,(
% 1.43/0.54    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f42])).
% 1.43/0.54  fof(f42,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.54    inference(nnf_transformation,[],[f30])).
% 1.43/0.54  fof(f30,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.54    inference(ennf_transformation,[],[f19])).
% 1.43/0.54  fof(f19,axiom,(
% 1.43/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 1.43/0.54  fof(f247,plain,(
% 1.43/0.54    spl3_8),
% 1.43/0.54    inference(avatar_contradiction_clause,[],[f246])).
% 1.43/0.54  fof(f246,plain,(
% 1.43/0.54    $false | spl3_8),
% 1.43/0.54    inference(subsumption_resolution,[],[f242,f59])).
% 1.43/0.54  fof(f59,plain,(
% 1.43/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f4])).
% 1.43/0.54  fof(f4,axiom,(
% 1.43/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.43/0.54  fof(f242,plain,(
% 1.43/0.54    ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl3_8),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f141,f76])).
% 1.43/0.54  fof(f76,plain,(
% 1.43/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f48])).
% 1.43/0.54  fof(f48,plain,(
% 1.43/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.43/0.54    inference(nnf_transformation,[],[f16])).
% 1.43/0.54  fof(f16,axiom,(
% 1.43/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.43/0.54  fof(f141,plain,(
% 1.43/0.54    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_8),
% 1.43/0.54    inference(avatar_component_clause,[],[f139])).
% 1.43/0.54  % SZS output end Proof for theBenchmark
% 1.43/0.54  % (13443)------------------------------
% 1.43/0.54  % (13443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (13443)Termination reason: Refutation
% 1.43/0.54  
% 1.43/0.54  % (13443)Memory used [KB]: 10746
% 1.43/0.54  % (13443)Time elapsed: 0.131 s
% 1.43/0.54  % (13443)------------------------------
% 1.43/0.54  % (13443)------------------------------
% 1.43/0.54  % (13416)Success in time 0.185 s
%------------------------------------------------------------------------------
