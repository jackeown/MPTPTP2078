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
% DateTime   : Thu Dec  3 13:15:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 132 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 ( 397 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7413)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f66,f103,f181])).

fof(f181,plain,
    ( ~ spl2_1
    | spl2_10 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl2_1
    | spl2_10 ),
    inference(resolution,[],[f172,f102])).

fof(f102,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_10
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f172,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl2_1 ),
    inference(superposition,[],[f31,f169])).

fof(f169,plain,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_1 ),
    inference(superposition,[],[f168,f166])).

fof(f166,plain,(
    ! [X0] : k4_xboole_0(k2_struct_0(sK0),X0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) ),
    inference(resolution,[],[f104,f24])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k4_xboole_0(k2_struct_0(X0),X1) ) ),
    inference(resolution,[],[f36,f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f36,plain,(
    ! [X2,X1] :
      ( ~ l1_struct_0(X1)
      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k4_xboole_0(k2_struct_0(X1),X2) ) ),
    inference(resolution,[],[f32,f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f168,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f42,f166])).

fof(f42,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_1
  <=> sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f103,plain,
    ( ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f99,f101,f44])).

fof(f44,plain,
    ( spl2_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f99,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f22,f98])).

fof(f98,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f96,f34])).

fof(f34,plain,(
    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(global_subsumption,[],[f24,f33])).

fof(f33,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f28,f23])).

fof(f23,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f96,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))
    | m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f56,f25])).

fof(f56,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK1,k1_tops_1(sK0,X0))
      | m2_connsp_2(X0,sK0,sK1) ) ),
    inference(global_subsumption,[],[f23,f24,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK1,k1_tops_1(sK0,X0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m2_connsp_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f22,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f66,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl2_2 ),
    inference(resolution,[],[f47,f24])).

fof(f47,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_2 ),
    inference(resolution,[],[f45,f27])).

fof(f45,plain,
    ( ~ l1_struct_0(sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f46,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f37,f44,f41])).

fof(f37,plain,
    ( ~ l1_struct_0(sK0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f26,f21])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:52:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.41  % (7409)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.42  % (7398)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.19/0.42  % (7420)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.19/0.43  % (7403)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.43  % (7412)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.19/0.43  % (7409)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % (7420)Refutation not found, incomplete strategy% (7420)------------------------------
% 0.19/0.43  % (7420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (7420)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.43  
% 0.19/0.43  % (7420)Memory used [KB]: 10618
% 0.19/0.43  % (7420)Time elapsed: 0.036 s
% 0.19/0.43  % (7420)------------------------------
% 0.19/0.43  % (7420)------------------------------
% 0.19/0.44  % (7403)Refutation not found, incomplete strategy% (7403)------------------------------
% 0.19/0.44  % (7403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % SZS output start Proof for theBenchmark
% 0.19/0.44  % (7413)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.19/0.44  fof(f182,plain,(
% 0.19/0.44    $false),
% 0.19/0.44    inference(avatar_sat_refutation,[],[f46,f66,f103,f181])).
% 0.19/0.44  fof(f181,plain,(
% 0.19/0.44    ~spl2_1 | spl2_10),
% 0.19/0.44    inference(avatar_contradiction_clause,[],[f180])).
% 0.19/0.44  fof(f180,plain,(
% 0.19/0.44    $false | (~spl2_1 | spl2_10)),
% 0.19/0.44    inference(resolution,[],[f172,f102])).
% 0.19/0.44  fof(f102,plain,(
% 0.19/0.44    ~r1_tarski(sK1,k2_struct_0(sK0)) | spl2_10),
% 0.19/0.44    inference(avatar_component_clause,[],[f101])).
% 0.19/0.44  fof(f101,plain,(
% 0.19/0.44    spl2_10 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.19/0.44  fof(f172,plain,(
% 0.19/0.44    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl2_1),
% 0.19/0.44    inference(superposition,[],[f31,f169])).
% 0.19/0.44  fof(f169,plain,(
% 0.19/0.44    sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_1),
% 0.19/0.44    inference(superposition,[],[f168,f166])).
% 0.19/0.44  fof(f166,plain,(
% 0.19/0.44    ( ! [X0] : (k4_xboole_0(k2_struct_0(sK0),X0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) )),
% 0.19/0.44    inference(resolution,[],[f104,f24])).
% 0.19/0.44  fof(f24,plain,(
% 0.19/0.44    l1_pre_topc(sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f12])).
% 0.19/0.44  fof(f12,plain,(
% 0.19/0.44    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.44    inference(flattening,[],[f11])).
% 0.19/0.44  fof(f11,plain,(
% 0.19/0.44    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f10])).
% 0.19/0.44  fof(f10,plain,(
% 0.19/0.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.19/0.44    inference(pure_predicate_removal,[],[f9])).
% 0.19/0.44  fof(f9,negated_conjecture,(
% 0.19/0.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.19/0.44    inference(negated_conjecture,[],[f8])).
% 0.19/0.44  fof(f8,conjecture,(
% 0.19/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).
% 0.19/0.44  fof(f104,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k4_xboole_0(k2_struct_0(X0),X1)) )),
% 0.19/0.44    inference(resolution,[],[f36,f27])).
% 0.19/0.44  fof(f27,plain,(
% 0.19/0.44    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f15])).
% 0.19/0.44  fof(f15,plain,(
% 0.19/0.44    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f4])).
% 0.19/0.44  fof(f4,axiom,(
% 0.19/0.44    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.44  fof(f36,plain,(
% 0.19/0.44    ( ! [X2,X1] : (~l1_struct_0(X1) | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k4_xboole_0(k2_struct_0(X1),X2)) )),
% 0.19/0.44    inference(resolution,[],[f32,f25])).
% 0.19/0.44  fof(f25,plain,(
% 0.19/0.44    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f13])).
% 0.19/0.44  fof(f13,plain,(
% 0.19/0.44    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f3])).
% 0.19/0.44  fof(f3,axiom,(
% 0.19/0.44    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.19/0.44  fof(f32,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f20])).
% 0.19/0.44  fof(f20,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f2])).
% 0.19/0.44  fof(f2,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.19/0.44  fof(f168,plain,(
% 0.19/0.44    sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_1),
% 0.19/0.44    inference(backward_demodulation,[],[f42,f166])).
% 0.19/0.44  fof(f42,plain,(
% 0.19/0.44    sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | ~spl2_1),
% 0.19/0.44    inference(avatar_component_clause,[],[f41])).
% 0.19/0.44  fof(f41,plain,(
% 0.19/0.44    spl2_1 <=> sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.44  fof(f31,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f1])).
% 0.19/0.44  fof(f1,axiom,(
% 0.19/0.44    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.44  fof(f103,plain,(
% 0.19/0.44    ~spl2_2 | ~spl2_10),
% 0.19/0.44    inference(avatar_split_clause,[],[f99,f101,f44])).
% 0.19/0.44  fof(f44,plain,(
% 0.19/0.44    spl2_2 <=> l1_struct_0(sK0)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.44  fof(f99,plain,(
% 0.19/0.44    ~r1_tarski(sK1,k2_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 0.19/0.44    inference(global_subsumption,[],[f22,f98])).
% 0.19/0.44  fof(f98,plain,(
% 0.19/0.44    ~r1_tarski(sK1,k2_struct_0(sK0)) | m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | ~l1_struct_0(sK0)),
% 0.19/0.44    inference(forward_demodulation,[],[f96,f34])).
% 0.19/0.44  fof(f34,plain,(
% 0.19/0.44    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.19/0.44    inference(global_subsumption,[],[f24,f33])).
% 0.19/0.44  fof(f33,plain,(
% 0.19/0.44    ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.19/0.44    inference(resolution,[],[f28,f23])).
% 0.19/0.44  fof(f23,plain,(
% 0.19/0.44    v2_pre_topc(sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f12])).
% 0.19/0.44  fof(f28,plain,(
% 0.19/0.44    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f17])).
% 0.19/0.44  fof(f17,plain,(
% 0.19/0.44    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.44    inference(flattening,[],[f16])).
% 0.19/0.44  fof(f16,plain,(
% 0.19/0.44    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f6])).
% 0.19/0.44  fof(f6,axiom,(
% 0.19/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 0.19/0.44  fof(f96,plain,(
% 0.19/0.44    ~r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | ~l1_struct_0(sK0)),
% 0.19/0.44    inference(resolution,[],[f56,f25])).
% 0.19/0.44  fof(f56,plain,(
% 0.19/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,k1_tops_1(sK0,X0)) | m2_connsp_2(X0,sK0,sK1)) )),
% 0.19/0.44    inference(global_subsumption,[],[f23,f24,f50])).
% 0.19/0.44  fof(f50,plain,(
% 0.19/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,k1_tops_1(sK0,X0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m2_connsp_2(X0,sK0,sK1)) )),
% 0.19/0.44    inference(resolution,[],[f29,f21])).
% 0.19/0.44  fof(f21,plain,(
% 0.19/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.44    inference(cnf_transformation,[],[f12])).
% 0.19/0.44  fof(f29,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m2_connsp_2(X2,X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f19])).
% 0.19/0.44  fof(f19,plain,(
% 0.19/0.44    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.44    inference(flattening,[],[f18])).
% 0.19/0.44  fof(f18,plain,(
% 0.19/0.44    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f7])).
% 0.19/0.44  fof(f7,axiom,(
% 0.19/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.19/0.44  fof(f22,plain,(
% 0.19/0.44    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f12])).
% 0.19/0.44  fof(f66,plain,(
% 0.19/0.44    spl2_2),
% 0.19/0.44    inference(avatar_contradiction_clause,[],[f65])).
% 0.19/0.44  fof(f65,plain,(
% 0.19/0.44    $false | spl2_2),
% 0.19/0.44    inference(resolution,[],[f47,f24])).
% 0.19/0.44  fof(f47,plain,(
% 0.19/0.44    ~l1_pre_topc(sK0) | spl2_2),
% 0.19/0.44    inference(resolution,[],[f45,f27])).
% 0.19/0.44  fof(f45,plain,(
% 0.19/0.44    ~l1_struct_0(sK0) | spl2_2),
% 0.19/0.44    inference(avatar_component_clause,[],[f44])).
% 0.19/0.44  fof(f46,plain,(
% 0.19/0.44    spl2_1 | ~spl2_2),
% 0.19/0.44    inference(avatar_split_clause,[],[f37,f44,f41])).
% 0.19/0.44  fof(f37,plain,(
% 0.19/0.44    ~l1_struct_0(sK0) | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))),
% 0.19/0.44    inference(resolution,[],[f26,f21])).
% 0.19/0.44  fof(f26,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) )),
% 0.19/0.44    inference(cnf_transformation,[],[f14])).
% 0.19/0.44  fof(f14,plain,(
% 0.19/0.44    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f5])).
% 0.19/0.44  fof(f5,axiom,(
% 0.19/0.44    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (7409)------------------------------
% 0.19/0.44  % (7409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (7409)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (7409)Memory used [KB]: 10746
% 0.19/0.44  % (7409)Time elapsed: 0.065 s
% 0.19/0.44  % (7409)------------------------------
% 0.19/0.44  % (7409)------------------------------
% 0.19/0.44  % (7396)Success in time 0.1 s
%------------------------------------------------------------------------------
