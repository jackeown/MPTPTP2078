%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:12 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   56 (  91 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  133 ( 263 expanded)
%              Number of equality atoms :   26 (  59 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f78,f88])).

fof(f88,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f86,f29])).

fof(f29,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f86,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f85,f75])).

fof(f75,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(resolution,[],[f62,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f62,plain,(
    ! [X0] : r1_tarski(k3_tarski(k1_xboole_0),X0) ),
    inference(superposition,[],[f45,f31])).

fof(f31,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k3_tarski(k1_xboole_0),k3_tarski(X0)) ),
    inference(resolution,[],[f34,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f85,plain,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f84,f25])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k1_xboole_0 = sK1
    & m1_setfam_1(sK1,u1_struct_0(sK0))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = X1
            & m1_setfam_1(X1,u1_struct_0(X0)) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(sK0)) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( k1_xboole_0 = X1
        & m1_setfam_1(X1,u1_struct_0(sK0)) )
   => ( k1_xboole_0 = sK1
      & m1_setfam_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

fof(f84,plain,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | v2_struct_0(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f82,f26])).

fof(f26,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f33,f58])).

fof(f58,plain,
    ( u1_struct_0(sK0) = k3_tarski(k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_2
  <=> u1_struct_0(sK0) = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f78,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f62,f54])).

fof(f54,plain,
    ( ~ r1_tarski(k3_tarski(k1_xboole_0),u1_struct_0(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_1
  <=> r1_tarski(k3_tarski(k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f59,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f49,f56,f52])).

fof(f49,plain,
    ( u1_struct_0(sK0) = k3_tarski(k1_xboole_0)
    | ~ r1_tarski(k3_tarski(k1_xboole_0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f44,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f44,plain,(
    r1_tarski(u1_struct_0(sK0),k3_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f38,f41])).

fof(f41,plain,(
    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f27,f28])).

fof(f28,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f27,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(X1,X0)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:18:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.46  % (460)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.18/0.49  % (476)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.18/0.49  % (457)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.18/0.49  % (465)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.18/0.50  % (465)Refutation found. Thanks to Tanya!
% 0.18/0.50  % SZS status Theorem for theBenchmark
% 0.18/0.50  % SZS output start Proof for theBenchmark
% 0.18/0.50  fof(f89,plain,(
% 0.18/0.50    $false),
% 0.18/0.50    inference(avatar_sat_refutation,[],[f59,f78,f88])).
% 0.18/0.50  fof(f88,plain,(
% 0.18/0.50    ~spl2_2),
% 0.18/0.50    inference(avatar_contradiction_clause,[],[f87])).
% 0.18/0.50  fof(f87,plain,(
% 0.18/0.50    $false | ~spl2_2),
% 0.18/0.50    inference(subsumption_resolution,[],[f86,f29])).
% 0.18/0.50  fof(f29,plain,(
% 0.18/0.50    v1_xboole_0(k1_xboole_0)),
% 0.18/0.50    inference(cnf_transformation,[],[f1])).
% 0.18/0.50  fof(f1,axiom,(
% 0.18/0.50    v1_xboole_0(k1_xboole_0)),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.18/0.50  fof(f86,plain,(
% 0.18/0.50    ~v1_xboole_0(k1_xboole_0) | ~spl2_2),
% 0.18/0.50    inference(forward_demodulation,[],[f85,f75])).
% 0.18/0.50  fof(f75,plain,(
% 0.18/0.50    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.18/0.50    inference(resolution,[],[f62,f32])).
% 0.18/0.50  fof(f32,plain,(
% 0.18/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.18/0.50    inference(cnf_transformation,[],[f15])).
% 0.18/0.50  fof(f15,plain,(
% 0.18/0.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.18/0.50    inference(ennf_transformation,[],[f4])).
% 0.18/0.50  fof(f4,axiom,(
% 0.18/0.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.18/0.50  fof(f62,plain,(
% 0.18/0.50    ( ! [X0] : (r1_tarski(k3_tarski(k1_xboole_0),X0)) )),
% 0.18/0.50    inference(superposition,[],[f45,f31])).
% 0.18/0.50  fof(f31,plain,(
% 0.18/0.50    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.18/0.50    inference(cnf_transformation,[],[f6])).
% 0.18/0.50  fof(f6,axiom,(
% 0.18/0.50    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.18/0.50  fof(f45,plain,(
% 0.18/0.50    ( ! [X0] : (r1_tarski(k3_tarski(k1_xboole_0),k3_tarski(X0))) )),
% 0.18/0.50    inference(resolution,[],[f34,f30])).
% 0.18/0.50  fof(f30,plain,(
% 0.18/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f3])).
% 0.18/0.50  fof(f3,axiom,(
% 0.18/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.18/0.50  fof(f34,plain,(
% 0.18/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) )),
% 0.18/0.50    inference(cnf_transformation,[],[f18])).
% 0.18/0.50  fof(f18,plain,(
% 0.18/0.50    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.18/0.50    inference(ennf_transformation,[],[f5])).
% 0.18/0.50  fof(f5,axiom,(
% 0.18/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.18/0.50  fof(f85,plain,(
% 0.18/0.50    ~v1_xboole_0(k3_tarski(k1_xboole_0)) | ~spl2_2),
% 0.18/0.50    inference(subsumption_resolution,[],[f84,f25])).
% 0.18/0.50  fof(f25,plain,(
% 0.18/0.50    ~v2_struct_0(sK0)),
% 0.18/0.50    inference(cnf_transformation,[],[f22])).
% 0.18/0.50  fof(f22,plain,(
% 0.18/0.50    (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.18/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21,f20])).
% 0.18/0.50  fof(f20,plain,(
% 0.18/0.50    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.18/0.50    introduced(choice_axiom,[])).
% 0.18/0.50  fof(f21,plain,(
% 0.18/0.50    ? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0))) => (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)))),
% 0.18/0.50    introduced(choice_axiom,[])).
% 0.18/0.50  fof(f14,plain,(
% 0.18/0.50    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.18/0.50    inference(flattening,[],[f13])).
% 0.18/0.50  fof(f13,plain,(
% 0.18/0.50    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.18/0.50    inference(ennf_transformation,[],[f12])).
% 0.18/0.50  fof(f12,plain,(
% 0.18/0.50    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))))),
% 0.18/0.50    inference(pure_predicate_removal,[],[f10])).
% 0.18/0.50  fof(f10,negated_conjecture,(
% 0.18/0.50    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.18/0.50    inference(negated_conjecture,[],[f9])).
% 0.18/0.50  fof(f9,conjecture,(
% 0.18/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).
% 0.18/0.50  fof(f84,plain,(
% 0.18/0.50    ~v1_xboole_0(k3_tarski(k1_xboole_0)) | v2_struct_0(sK0) | ~spl2_2),
% 0.18/0.50    inference(subsumption_resolution,[],[f82,f26])).
% 0.18/0.50  fof(f26,plain,(
% 0.18/0.50    l1_struct_0(sK0)),
% 0.18/0.50    inference(cnf_transformation,[],[f22])).
% 0.18/0.50  fof(f82,plain,(
% 0.18/0.50    ~v1_xboole_0(k3_tarski(k1_xboole_0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl2_2),
% 0.18/0.50    inference(superposition,[],[f33,f58])).
% 0.18/0.50  fof(f58,plain,(
% 0.18/0.50    u1_struct_0(sK0) = k3_tarski(k1_xboole_0) | ~spl2_2),
% 0.18/0.50    inference(avatar_component_clause,[],[f56])).
% 0.18/0.50  fof(f56,plain,(
% 0.18/0.50    spl2_2 <=> u1_struct_0(sK0) = k3_tarski(k1_xboole_0)),
% 0.18/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.18/0.50  fof(f33,plain,(
% 0.18/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f17])).
% 0.18/0.50  fof(f17,plain,(
% 0.18/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.18/0.50    inference(flattening,[],[f16])).
% 0.18/0.50  fof(f16,plain,(
% 0.18/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.18/0.50    inference(ennf_transformation,[],[f8])).
% 0.18/0.50  fof(f8,axiom,(
% 0.18/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.18/0.50  fof(f78,plain,(
% 0.18/0.50    spl2_1),
% 0.18/0.50    inference(avatar_contradiction_clause,[],[f74])).
% 0.18/0.50  fof(f74,plain,(
% 0.18/0.50    $false | spl2_1),
% 0.18/0.50    inference(resolution,[],[f62,f54])).
% 0.18/0.50  fof(f54,plain,(
% 0.18/0.50    ~r1_tarski(k3_tarski(k1_xboole_0),u1_struct_0(sK0)) | spl2_1),
% 0.18/0.50    inference(avatar_component_clause,[],[f52])).
% 0.18/0.50  fof(f52,plain,(
% 0.18/0.50    spl2_1 <=> r1_tarski(k3_tarski(k1_xboole_0),u1_struct_0(sK0))),
% 0.18/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.18/0.50  fof(f59,plain,(
% 0.18/0.50    ~spl2_1 | spl2_2),
% 0.18/0.50    inference(avatar_split_clause,[],[f49,f56,f52])).
% 0.18/0.50  fof(f49,plain,(
% 0.18/0.50    u1_struct_0(sK0) = k3_tarski(k1_xboole_0) | ~r1_tarski(k3_tarski(k1_xboole_0),u1_struct_0(sK0))),
% 0.18/0.50    inference(resolution,[],[f44,f37])).
% 0.18/0.50  fof(f37,plain,(
% 0.18/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f24])).
% 0.18/0.50  fof(f24,plain,(
% 0.18/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.18/0.50    inference(flattening,[],[f23])).
% 0.18/0.50  fof(f23,plain,(
% 0.18/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.18/0.50    inference(nnf_transformation,[],[f2])).
% 0.18/0.50  fof(f2,axiom,(
% 0.18/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.18/0.50  fof(f44,plain,(
% 0.18/0.50    r1_tarski(u1_struct_0(sK0),k3_tarski(k1_xboole_0))),
% 0.18/0.50    inference(resolution,[],[f38,f41])).
% 0.18/0.50  fof(f41,plain,(
% 0.18/0.50    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 0.18/0.50    inference(forward_demodulation,[],[f27,f28])).
% 0.18/0.50  fof(f28,plain,(
% 0.18/0.50    k1_xboole_0 = sK1),
% 0.18/0.50    inference(cnf_transformation,[],[f22])).
% 0.18/0.50  fof(f27,plain,(
% 0.18/0.50    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.18/0.50    inference(cnf_transformation,[],[f22])).
% 0.18/0.50  fof(f38,plain,(
% 0.18/0.50    ( ! [X0,X1] : (~m1_setfam_1(X1,X0) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.18/0.50    inference(cnf_transformation,[],[f19])).
% 0.18/0.50  fof(f19,plain,(
% 0.18/0.50    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0))),
% 0.18/0.50    inference(ennf_transformation,[],[f11])).
% 0.18/0.50  fof(f11,plain,(
% 0.18/0.50    ! [X0,X1] : (m1_setfam_1(X1,X0) => r1_tarski(X0,k3_tarski(X1)))),
% 0.18/0.50    inference(unused_predicate_definition_removal,[],[f7])).
% 0.18/0.50  fof(f7,axiom,(
% 0.18/0.50    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.18/0.50  % SZS output end Proof for theBenchmark
% 0.18/0.50  % (465)------------------------------
% 0.18/0.50  % (465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.50  % (465)Termination reason: Refutation
% 0.18/0.50  
% 0.18/0.50  % (465)Memory used [KB]: 10618
% 0.18/0.50  % (465)Time elapsed: 0.092 s
% 0.18/0.50  % (465)------------------------------
% 0.18/0.50  % (465)------------------------------
% 0.18/0.50  % (454)Success in time 0.156 s
%------------------------------------------------------------------------------
