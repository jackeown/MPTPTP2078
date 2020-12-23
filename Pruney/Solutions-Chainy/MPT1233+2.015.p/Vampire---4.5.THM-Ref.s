%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:58 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 130 expanded)
%              Number of leaves         :   22 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  202 ( 286 expanded)
%              Number of equality atoms :   47 (  70 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (19479)Termination reason: Refutation not found, incomplete strategy

% (19479)Memory used [KB]: 6268
% (19479)Time elapsed: 0.165 s
% (19479)------------------------------
% (19479)------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f78,f84,f90,f112,f125,f148])).

fof(f148,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f147,f122,f59,f87])).

% (19462)Refutation not found, incomplete strategy% (19462)------------------------------
% (19462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19462)Termination reason: Refutation not found, incomplete strategy

% (19462)Memory used [KB]: 10618
% (19462)Time elapsed: 0.147 s
% (19462)------------------------------
% (19462)------------------------------
fof(f87,plain,
    ( spl2_7
  <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f59,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f122,plain,
    ( spl2_9
  <=> k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

% (19455)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f147,plain,
    ( u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f146,f52])).

fof(f52,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f37,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f146,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f145,f124])).

fof(f124,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f145,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl2_2 ),
    inference(resolution,[],[f119,f61])).

fof(f61,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f119,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f117,f101])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f99,f52])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f44,f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f117,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    inference(resolution,[],[f40,f96])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f94,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f94,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f47,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f125,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f120,f109,f59,f122])).

fof(f109,plain,
    ( spl2_8
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl2_8 ),
    inference(resolution,[],[f105,f111])).

fof(f111,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k2_pre_topc(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f42,f36])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f112,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f107,f59,f64,f109])).

fof(f64,plain,
    ( spl2_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f107,plain,
    ( ~ v2_pre_topc(sK0)
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f104,f61])).

fof(f104,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(k1_xboole_0,X0) ) ),
    inference(global_subsumption,[],[f33,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(k1_xboole_0)
      | v4_pre_topc(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f43,f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f90,plain,
    ( ~ spl2_7
    | spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f85,f81,f54,f87])).

fof(f54,plain,
    ( spl2_1
  <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f81,plain,
    ( spl2_6
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f85,plain,
    ( u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))
    | spl2_1
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f56,f83])).

fof(f83,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f56,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f84,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f79,f75,f81])).

fof(f75,plain,
    ( spl2_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

% (19464)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (19489)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f79,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f38,f77])).

fof(f77,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f78,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f73,f59,f75])).

fof(f73,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f39,f61])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f67,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f30,f64])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f62,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f31,f59])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f32,f54])).

fof(f32,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:01:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.47  % (19456)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (19456)Refutation not found, incomplete strategy% (19456)------------------------------
% 0.22/0.47  % (19456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (19456)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (19456)Memory used [KB]: 6140
% 0.22/0.47  % (19456)Time elapsed: 0.050 s
% 0.22/0.47  % (19456)------------------------------
% 0.22/0.47  % (19456)------------------------------
% 0.22/0.47  % (19476)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.48  % (19476)Refutation not found, incomplete strategy% (19476)------------------------------
% 0.22/0.48  % (19476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (19476)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (19476)Memory used [KB]: 10746
% 0.22/0.48  % (19476)Time elapsed: 0.061 s
% 0.22/0.48  % (19476)------------------------------
% 0.22/0.48  % (19476)------------------------------
% 0.22/0.54  % (19461)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (19453)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (19454)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.48/0.56  % (19457)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.48/0.56  % (19477)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.48/0.56  % (19470)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.48/0.56  % (19472)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.48/0.56  % (19454)Refutation not found, incomplete strategy% (19454)------------------------------
% 1.48/0.56  % (19454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (19479)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.57  % (19481)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.48/0.57  % (19461)Refutation not found, incomplete strategy% (19461)------------------------------
% 1.48/0.57  % (19461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (19462)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.48/0.57  % (19454)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (19454)Memory used [KB]: 10618
% 1.48/0.57  % (19454)Time elapsed: 0.133 s
% 1.48/0.57  % (19454)------------------------------
% 1.48/0.57  % (19454)------------------------------
% 1.48/0.57  % (19457)Refutation not found, incomplete strategy% (19457)------------------------------
% 1.48/0.57  % (19457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (19468)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.48/0.57  % (19457)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (19457)Memory used [KB]: 6268
% 1.48/0.57  % (19457)Time elapsed: 0.132 s
% 1.48/0.57  % (19457)------------------------------
% 1.48/0.57  % (19457)------------------------------
% 1.48/0.57  % (19461)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (19461)Memory used [KB]: 10618
% 1.48/0.57  % (19461)Time elapsed: 0.144 s
% 1.48/0.57  % (19461)------------------------------
% 1.48/0.57  % (19461)------------------------------
% 1.48/0.57  % (19469)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.48/0.57  % (19469)Refutation not found, incomplete strategy% (19469)------------------------------
% 1.48/0.57  % (19469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (19469)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (19469)Memory used [KB]: 6140
% 1.48/0.57  % (19469)Time elapsed: 0.001 s
% 1.48/0.57  % (19469)------------------------------
% 1.48/0.57  % (19469)------------------------------
% 1.48/0.57  % (19480)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.58  % (19479)Refutation not found, incomplete strategy% (19479)------------------------------
% 1.48/0.58  % (19479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (19470)Refutation found. Thanks to Tanya!
% 1.48/0.58  % SZS status Theorem for theBenchmark
% 1.48/0.58  % SZS output start Proof for theBenchmark
% 1.48/0.58  % (19479)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.58  
% 1.48/0.58  % (19479)Memory used [KB]: 6268
% 1.48/0.58  % (19479)Time elapsed: 0.165 s
% 1.48/0.58  % (19479)------------------------------
% 1.48/0.58  % (19479)------------------------------
% 1.48/0.58  fof(f149,plain,(
% 1.48/0.58    $false),
% 1.48/0.58    inference(avatar_sat_refutation,[],[f57,f62,f67,f78,f84,f90,f112,f125,f148])).
% 1.48/0.58  fof(f148,plain,(
% 1.48/0.58    spl2_7 | ~spl2_2 | ~spl2_9),
% 1.48/0.58    inference(avatar_split_clause,[],[f147,f122,f59,f87])).
% 1.48/0.58  % (19462)Refutation not found, incomplete strategy% (19462)------------------------------
% 1.48/0.58  % (19462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (19462)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.58  
% 1.48/0.58  % (19462)Memory used [KB]: 10618
% 1.48/0.58  % (19462)Time elapsed: 0.147 s
% 1.48/0.58  % (19462)------------------------------
% 1.48/0.58  % (19462)------------------------------
% 1.48/0.58  fof(f87,plain,(
% 1.48/0.58    spl2_7 <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.48/0.58  fof(f59,plain,(
% 1.48/0.58    spl2_2 <=> l1_pre_topc(sK0)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.48/0.58  fof(f122,plain,(
% 1.48/0.58    spl2_9 <=> k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.48/0.58  % (19455)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.48/0.58  fof(f147,plain,(
% 1.48/0.58    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) | (~spl2_2 | ~spl2_9)),
% 1.48/0.58    inference(forward_demodulation,[],[f146,f52])).
% 1.48/0.58  fof(f52,plain,(
% 1.48/0.58    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.48/0.58    inference(definition_unfolding,[],[f35,f51])).
% 1.48/0.58  fof(f51,plain,(
% 1.48/0.58    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f37,f34])).
% 1.48/0.58  fof(f34,plain,(
% 1.48/0.58    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f3])).
% 1.48/0.58  fof(f3,axiom,(
% 1.48/0.58    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.48/0.58  fof(f37,plain,(
% 1.48/0.58    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f6])).
% 1.48/0.58  fof(f6,axiom,(
% 1.48/0.58    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 1.48/0.58  fof(f35,plain,(
% 1.48/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.48/0.58    inference(cnf_transformation,[],[f4])).
% 1.48/0.58  fof(f4,axiom,(
% 1.48/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.48/0.58  fof(f146,plain,(
% 1.48/0.58    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | (~spl2_2 | ~spl2_9)),
% 1.48/0.58    inference(forward_demodulation,[],[f145,f124])).
% 1.48/0.58  fof(f124,plain,(
% 1.48/0.58    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | ~spl2_9),
% 1.48/0.58    inference(avatar_component_clause,[],[f122])).
% 1.48/0.58  fof(f145,plain,(
% 1.48/0.58    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) | ~spl2_2),
% 1.48/0.58    inference(resolution,[],[f119,f61])).
% 1.48/0.58  fof(f61,plain,(
% 1.48/0.58    l1_pre_topc(sK0) | ~spl2_2),
% 1.48/0.58    inference(avatar_component_clause,[],[f59])).
% 1.48/0.58  fof(f119,plain,(
% 1.48/0.58    ( ! [X1] : (~l1_pre_topc(X1) | k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_xboole_0))) )),
% 1.48/0.58    inference(forward_demodulation,[],[f117,f101])).
% 1.48/0.58  fof(f101,plain,(
% 1.48/0.58    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.48/0.58    inference(forward_demodulation,[],[f99,f52])).
% 1.48/0.58  fof(f99,plain,(
% 1.48/0.58    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.48/0.58    inference(resolution,[],[f44,f36])).
% 1.48/0.58  fof(f36,plain,(
% 1.48/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f7])).
% 1.48/0.58  fof(f7,axiom,(
% 1.48/0.58    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.48/0.58  fof(f44,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.48/0.58    inference(cnf_transformation,[],[f26])).
% 1.48/0.58  fof(f26,plain,(
% 1.48/0.58    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.48/0.58    inference(ennf_transformation,[],[f5])).
% 1.48/0.58  fof(f5,axiom,(
% 1.48/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.48/0.58  fof(f117,plain,(
% 1.48/0.58    ( ! [X1] : (~l1_pre_topc(X1) | k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),u1_struct_0(X1))))) )),
% 1.48/0.58    inference(resolution,[],[f40,f96])).
% 1.48/0.58  fof(f96,plain,(
% 1.48/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.48/0.58    inference(resolution,[],[f94,f48])).
% 1.48/0.58  fof(f48,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f8])).
% 1.48/0.58  fof(f8,axiom,(
% 1.48/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.48/0.58  fof(f94,plain,(
% 1.48/0.58    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.48/0.58    inference(duplicate_literal_removal,[],[f93])).
% 1.48/0.58  fof(f93,plain,(
% 1.48/0.58    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.48/0.58    inference(resolution,[],[f47,f46])).
% 1.48/0.58  fof(f46,plain,(
% 1.48/0.58    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f27])).
% 1.48/0.58  fof(f27,plain,(
% 1.48/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.48/0.58    inference(ennf_transformation,[],[f1])).
% 1.48/0.58  fof(f1,axiom,(
% 1.48/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.48/0.58  fof(f47,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~r2_hidden(sK1(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f27])).
% 1.48/0.58  fof(f40,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f21])).
% 1.48/0.58  fof(f21,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f14])).
% 1.48/0.58  fof(f14,axiom,(
% 1.48/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 1.48/0.58  fof(f125,plain,(
% 1.48/0.58    spl2_9 | ~spl2_2 | ~spl2_8),
% 1.48/0.58    inference(avatar_split_clause,[],[f120,f109,f59,f122])).
% 1.48/0.58  fof(f109,plain,(
% 1.48/0.58    spl2_8 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.48/0.58  fof(f120,plain,(
% 1.48/0.58    ~l1_pre_topc(sK0) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | ~spl2_8),
% 1.48/0.58    inference(resolution,[],[f105,f111])).
% 1.48/0.58  fof(f111,plain,(
% 1.48/0.58    v4_pre_topc(k1_xboole_0,sK0) | ~spl2_8),
% 1.48/0.58    inference(avatar_component_clause,[],[f109])).
% 1.48/0.58  fof(f105,plain,(
% 1.48/0.58    ( ! [X0] : (~v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0) | k1_xboole_0 = k2_pre_topc(X0,k1_xboole_0)) )),
% 1.48/0.58    inference(resolution,[],[f42,f36])).
% 1.48/0.58  fof(f42,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.48/0.58    inference(cnf_transformation,[],[f23])).
% 1.48/0.58  fof(f23,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.48/0.58    inference(flattening,[],[f22])).
% 1.48/0.58  fof(f22,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f13])).
% 1.48/0.58  fof(f13,axiom,(
% 1.48/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.48/0.58  fof(f112,plain,(
% 1.48/0.58    spl2_8 | ~spl2_3 | ~spl2_2),
% 1.48/0.58    inference(avatar_split_clause,[],[f107,f59,f64,f109])).
% 1.48/0.58  fof(f64,plain,(
% 1.48/0.58    spl2_3 <=> v2_pre_topc(sK0)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.48/0.58  fof(f107,plain,(
% 1.48/0.58    ~v2_pre_topc(sK0) | v4_pre_topc(k1_xboole_0,sK0) | ~spl2_2),
% 1.48/0.58    inference(resolution,[],[f104,f61])).
% 1.48/0.58  fof(f104,plain,(
% 1.48/0.58    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v4_pre_topc(k1_xboole_0,X0)) )),
% 1.48/0.58    inference(global_subsumption,[],[f33,f102])).
% 1.48/0.58  fof(f102,plain,(
% 1.48/0.58    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(k1_xboole_0) | v4_pre_topc(k1_xboole_0,X0)) )),
% 1.48/0.58    inference(resolution,[],[f43,f36])).
% 1.48/0.58  fof(f43,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f25])).
% 1.48/0.58  fof(f25,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.48/0.58    inference(flattening,[],[f24])).
% 1.48/0.58  fof(f24,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.48/0.58    inference(ennf_transformation,[],[f10])).
% 1.48/0.58  fof(f10,axiom,(
% 1.48/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 1.48/0.58  fof(f33,plain,(
% 1.48/0.58    v1_xboole_0(k1_xboole_0)),
% 1.48/0.58    inference(cnf_transformation,[],[f2])).
% 1.48/0.58  fof(f2,axiom,(
% 1.48/0.58    v1_xboole_0(k1_xboole_0)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.48/0.58  fof(f90,plain,(
% 1.48/0.58    ~spl2_7 | spl2_1 | ~spl2_6),
% 1.48/0.58    inference(avatar_split_clause,[],[f85,f81,f54,f87])).
% 1.48/0.58  fof(f54,plain,(
% 1.48/0.58    spl2_1 <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.48/0.58  fof(f81,plain,(
% 1.48/0.58    spl2_6 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.48/0.58  fof(f85,plain,(
% 1.48/0.58    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) | (spl2_1 | ~spl2_6)),
% 1.48/0.58    inference(backward_demodulation,[],[f56,f83])).
% 1.48/0.58  fof(f83,plain,(
% 1.48/0.58    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl2_6),
% 1.48/0.58    inference(avatar_component_clause,[],[f81])).
% 1.48/0.58  fof(f56,plain,(
% 1.48/0.58    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) | spl2_1),
% 1.48/0.58    inference(avatar_component_clause,[],[f54])).
% 1.48/0.58  fof(f84,plain,(
% 1.48/0.58    spl2_6 | ~spl2_5),
% 1.48/0.58    inference(avatar_split_clause,[],[f79,f75,f81])).
% 1.48/0.58  fof(f75,plain,(
% 1.48/0.58    spl2_5 <=> l1_struct_0(sK0)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.48/0.58  % (19464)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.48/0.58  % (19489)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.48/0.58  fof(f79,plain,(
% 1.48/0.58    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl2_5),
% 1.48/0.58    inference(resolution,[],[f38,f77])).
% 1.48/0.58  fof(f77,plain,(
% 1.48/0.58    l1_struct_0(sK0) | ~spl2_5),
% 1.48/0.58    inference(avatar_component_clause,[],[f75])).
% 1.48/0.58  fof(f38,plain,(
% 1.48/0.58    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f19])).
% 1.48/0.58  fof(f19,plain,(
% 1.48/0.58    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f11])).
% 1.48/0.58  fof(f11,axiom,(
% 1.48/0.58    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.48/0.58  fof(f78,plain,(
% 1.48/0.58    spl2_5 | ~spl2_2),
% 1.48/0.58    inference(avatar_split_clause,[],[f73,f59,f75])).
% 1.48/0.58  fof(f73,plain,(
% 1.48/0.58    l1_struct_0(sK0) | ~spl2_2),
% 1.48/0.58    inference(resolution,[],[f39,f61])).
% 1.48/0.58  fof(f39,plain,(
% 1.48/0.58    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f20])).
% 1.48/0.58  fof(f20,plain,(
% 1.48/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f12])).
% 1.48/0.58  fof(f12,axiom,(
% 1.48/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.48/0.58  fof(f67,plain,(
% 1.48/0.58    spl2_3),
% 1.48/0.58    inference(avatar_split_clause,[],[f30,f64])).
% 1.48/0.58  fof(f30,plain,(
% 1.48/0.58    v2_pre_topc(sK0)),
% 1.48/0.58    inference(cnf_transformation,[],[f18])).
% 1.48/0.58  fof(f18,plain,(
% 1.48/0.58    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.48/0.58    inference(flattening,[],[f17])).
% 1.48/0.58  fof(f17,plain,(
% 1.48/0.58    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.48/0.58    inference(ennf_transformation,[],[f16])).
% 1.48/0.58  fof(f16,negated_conjecture,(
% 1.48/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.48/0.58    inference(negated_conjecture,[],[f15])).
% 1.48/0.58  fof(f15,conjecture,(
% 1.48/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 1.48/0.58  fof(f62,plain,(
% 1.48/0.58    spl2_2),
% 1.48/0.58    inference(avatar_split_clause,[],[f31,f59])).
% 1.48/0.58  fof(f31,plain,(
% 1.48/0.58    l1_pre_topc(sK0)),
% 1.48/0.58    inference(cnf_transformation,[],[f18])).
% 1.48/0.58  fof(f57,plain,(
% 1.48/0.58    ~spl2_1),
% 1.48/0.58    inference(avatar_split_clause,[],[f32,f54])).
% 1.48/0.58  fof(f32,plain,(
% 1.48/0.58    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 1.48/0.58    inference(cnf_transformation,[],[f18])).
% 1.48/0.58  % SZS output end Proof for theBenchmark
% 1.48/0.58  % (19470)------------------------------
% 1.48/0.58  % (19470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (19470)Termination reason: Refutation
% 1.48/0.58  
% 1.48/0.58  % (19470)Memory used [KB]: 10746
% 1.48/0.58  % (19470)Time elapsed: 0.145 s
% 1.48/0.58  % (19470)------------------------------
% 1.48/0.58  % (19470)------------------------------
% 1.48/0.58  % (19489)Refutation not found, incomplete strategy% (19489)------------------------------
% 1.48/0.58  % (19489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (19489)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.58  
% 1.48/0.58  % (19489)Memory used [KB]: 6268
% 1.48/0.58  % (19489)Time elapsed: 0.027 s
% 1.48/0.58  % (19489)------------------------------
% 1.48/0.58  % (19489)------------------------------
% 1.48/0.58  % (19464)Refutation not found, incomplete strategy% (19464)------------------------------
% 1.48/0.58  % (19464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (19464)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.58  
% 1.48/0.58  % (19464)Memory used [KB]: 10618
% 1.48/0.58  % (19464)Time elapsed: 0.156 s
% 1.48/0.58  % (19464)------------------------------
% 1.48/0.58  % (19464)------------------------------
% 1.76/0.58  % (19448)Success in time 0.216 s
%------------------------------------------------------------------------------
