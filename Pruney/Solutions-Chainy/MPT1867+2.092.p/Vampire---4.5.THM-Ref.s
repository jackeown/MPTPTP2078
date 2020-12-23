%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:18 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 201 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  191 ( 722 expanded)
%              Number of equality atoms :   28 (  61 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f205,f387])).

fof(f387,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f385,f174])).

fof(f174,plain,(
    k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f67,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f67,plain,(
    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f66,f42])).

fof(f42,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f24,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f24,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f66,plain,(
    r1_tarski(sK2(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f65,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f58,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2(sK0,sK1),sK1) ),
    inference(resolution,[],[f26,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(f26,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f385,plain,
    ( k1_xboole_0 != sK2(sK0,k1_xboole_0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f378,f353])).

fof(f353,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f323,f35])).

fof(f323,plain,(
    ! [X0] : v1_xboole_0(k3_xboole_0(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f41,f132])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f69,f38])).

fof(f69,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f24,f42])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f378,plain,
    ( sK2(sK0,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f68,f39,f107])).

fof(f107,plain,
    ( ! [X1] :
        ( sK2(sK0,X1) != k3_xboole_0(X1,k1_xboole_0)
        | v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_2
  <=> ! [X1] :
        ( sK2(sK0,X1) != k3_xboole_0(X1,k1_xboole_0)
        | v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f68,plain,(
    ~ v2_tex_2(k1_xboole_0,sK0) ),
    inference(superposition,[],[f26,f42])).

fof(f205,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f203,f39])).

fof(f203,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f202,f28])).

fof(f202,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f201,f27])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f201,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f198,f104])).

fof(f104,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_1
  <=> v3_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f198,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f36,f155])).

fof(f155,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f47,f38])).

fof(f47,plain,(
    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f39,f28,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f108,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f100,f106,f102])).

fof(f100,plain,(
    ! [X1] :
      ( sK2(sK0,X1) != k3_xboole_0(X1,k1_xboole_0)
      | ~ v3_pre_topc(k1_xboole_0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X1,sK0) ) ),
    inference(forward_demodulation,[],[f99,f89])).

fof(f89,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f74,f42])).

fof(f74,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(unit_resulting_resolution,[],[f25,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f99,plain,(
    ! [X1] :
      ( sK2(sK0,X1) != k9_subset_1(u1_struct_0(sK0),X1,k1_xboole_0)
      | ~ v3_pre_topc(k1_xboole_0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X1,sK0) ) ),
    inference(forward_demodulation,[],[f98,f42])).

fof(f98,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k1_xboole_0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(sK0,X1) != k9_subset_1(u1_struct_0(sK0),X1,sK1)
      | v2_tex_2(X1,sK0) ) ),
    inference(forward_demodulation,[],[f97,f42])).

fof(f97,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0)
      | sK2(sK0,X1) != k9_subset_1(u1_struct_0(sK0),X1,sK1)
      | v2_tex_2(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f76,f28])).

fof(f76,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0)
      | sK2(sK0,X1) != k9_subset_1(u1_struct_0(sK0),X1,sK1)
      | v2_tex_2(X1,sK0) ) ),
    inference(resolution,[],[f25,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n015.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 14:03:23 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.48  % (15813)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.49  % (15807)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.49  % (15805)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.49  % (15804)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.50  % (15813)Refutation not found, incomplete strategy% (15813)------------------------------
% 0.19/0.50  % (15813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (15813)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (15813)Memory used [KB]: 10618
% 0.19/0.50  % (15813)Time elapsed: 0.112 s
% 0.19/0.50  % (15813)------------------------------
% 0.19/0.50  % (15813)------------------------------
% 0.19/0.50  % (15796)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.50  % (15821)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.50  % (15799)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.50  % (15805)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f388,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f108,f205,f387])).
% 0.19/0.50  fof(f387,plain,(
% 0.19/0.50    ~spl4_2),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f386])).
% 0.19/0.50  fof(f386,plain,(
% 0.19/0.50    $false | ~spl4_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f385,f174])).
% 0.19/0.50  fof(f174,plain,(
% 0.19/0.50    k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f67,f38])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f22])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.19/0.50    inference(ennf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.19/0.50  fof(f67,plain,(
% 0.19/0.50    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)),
% 0.19/0.50    inference(forward_demodulation,[],[f66,f42])).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    k1_xboole_0 = sK1),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f24,f35])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    v1_xboole_0(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f15])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.50    inference(flattening,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f13])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.19/0.50    inference(pure_predicate_removal,[],[f12])).
% 0.19/0.50  fof(f12,negated_conjecture,(
% 0.19/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.19/0.50    inference(negated_conjecture,[],[f11])).
% 0.19/0.50  fof(f11,conjecture,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.19/0.50  fof(f66,plain,(
% 0.19/0.50    r1_tarski(sK2(sK0,sK1),sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f65,f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.50    inference(cnf_transformation,[],[f15])).
% 0.19/0.50  fof(f65,plain,(
% 0.19/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2(sK0,sK1),sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f58,f28])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    l1_pre_topc(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f15])).
% 0.19/0.50  fof(f58,plain,(
% 0.19/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2(sK0,sK1),sK1)),
% 0.19/0.50    inference(resolution,[],[f26,f34])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.51    inference(flattening,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ~v2_tex_2(sK1,sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f385,plain,(
% 0.19/0.51    k1_xboole_0 != sK2(sK0,k1_xboole_0) | ~spl4_2),
% 0.19/0.51    inference(forward_demodulation,[],[f378,f353])).
% 0.19/0.51  fof(f353,plain,(
% 0.19/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f323,f35])).
% 0.19/0.51  fof(f323,plain,(
% 0.19/0.51    ( ! [X0] : (v1_xboole_0(k3_xboole_0(k1_xboole_0,X0))) )),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f41,f132])).
% 0.19/0.51  fof(f132,plain,(
% 0.19/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 0.19/0.51    inference(superposition,[],[f69,f38])).
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    v1_xboole_0(k1_xboole_0)),
% 0.19/0.51    inference(superposition,[],[f24,f42])).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.19/0.51  fof(f378,plain,(
% 0.19/0.51    sK2(sK0,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_2),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f68,f39,f107])).
% 0.19/0.51  fof(f107,plain,(
% 0.19/0.51    ( ! [X1] : (sK2(sK0,X1) != k3_xboole_0(X1,k1_xboole_0) | v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f106])).
% 0.19/0.51  fof(f106,plain,(
% 0.19/0.51    spl4_2 <=> ! [X1] : (sK2(sK0,X1) != k3_xboole_0(X1,k1_xboole_0) | v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    ~v2_tex_2(k1_xboole_0,sK0)),
% 0.19/0.51    inference(superposition,[],[f26,f42])).
% 0.19/0.51  fof(f205,plain,(
% 0.19/0.51    spl4_1),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f204])).
% 0.19/0.51  fof(f204,plain,(
% 0.19/0.51    $false | spl4_1),
% 0.19/0.51    inference(subsumption_resolution,[],[f203,f39])).
% 0.19/0.51  fof(f203,plain,(
% 0.19/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_1),
% 0.19/0.51    inference(subsumption_resolution,[],[f202,f28])).
% 0.19/0.51  fof(f202,plain,(
% 0.19/0.51    ~l1_pre_topc(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_1),
% 0.19/0.51    inference(subsumption_resolution,[],[f201,f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    v2_pre_topc(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f201,plain,(
% 0.19/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_1),
% 0.19/0.51    inference(subsumption_resolution,[],[f198,f104])).
% 0.19/0.51  fof(f104,plain,(
% 0.19/0.51    ~v3_pre_topc(k1_xboole_0,sK0) | spl4_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f102])).
% 0.19/0.51  fof(f102,plain,(
% 0.19/0.51    spl4_1 <=> v3_pre_topc(k1_xboole_0,sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.51  fof(f198,plain,(
% 0.19/0.51    v3_pre_topc(k1_xboole_0,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.51    inference(superposition,[],[f36,f155])).
% 0.19/0.51  fof(f155,plain,(
% 0.19/0.51    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f47,f38])).
% 0.19/0.51  fof(f47,plain,(
% 0.19/0.51    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f39,f28,f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.51    inference(flattening,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.19/0.51  fof(f108,plain,(
% 0.19/0.51    ~spl4_1 | spl4_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f100,f106,f102])).
% 0.19/0.51  fof(f100,plain,(
% 0.19/0.51    ( ! [X1] : (sK2(sK0,X1) != k3_xboole_0(X1,k1_xboole_0) | ~v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0)) )),
% 0.19/0.51    inference(forward_demodulation,[],[f99,f89])).
% 0.19/0.51  fof(f89,plain,(
% 0.19/0.51    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.51    inference(forward_demodulation,[],[f74,f42])).
% 0.19/0.51  fof(f74,plain,(
% 0.19/0.51    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)) )),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f25,f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.19/0.51  fof(f99,plain,(
% 0.19/0.51    ( ! [X1] : (sK2(sK0,X1) != k9_subset_1(u1_struct_0(sK0),X1,k1_xboole_0) | ~v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0)) )),
% 0.19/0.51    inference(forward_demodulation,[],[f98,f42])).
% 0.19/0.51  fof(f98,plain,(
% 0.19/0.51    ( ! [X1] : (~v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(sK0,X1) != k9_subset_1(u1_struct_0(sK0),X1,sK1) | v2_tex_2(X1,sK0)) )),
% 0.19/0.51    inference(forward_demodulation,[],[f97,f42])).
% 0.19/0.51  fof(f97,plain,(
% 0.19/0.51    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | sK2(sK0,X1) != k9_subset_1(u1_struct_0(sK0),X1,sK1) | v2_tex_2(X1,sK0)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f76,f28])).
% 0.19/0.51  fof(f76,plain,(
% 0.19/0.51    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | sK2(sK0,X1) != k9_subset_1(u1_struct_0(sK0),X1,sK1) | v2_tex_2(X1,sK0)) )),
% 0.19/0.51    inference(resolution,[],[f25,f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (15805)------------------------------
% 0.19/0.51  % (15805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (15805)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (15805)Memory used [KB]: 10746
% 0.19/0.51  % (15805)Time elapsed: 0.111 s
% 0.19/0.51  % (15805)------------------------------
% 0.19/0.51  % (15805)------------------------------
% 0.19/0.51  % (15795)Success in time 0.17 s
%------------------------------------------------------------------------------
