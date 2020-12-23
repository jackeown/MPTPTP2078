%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:24 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 124 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   15
%              Number of atoms          :  193 ( 573 expanded)
%              Number of equality atoms :   17 (  65 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f85,f132,f147,f176])).

fof(f176,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f171,f127])).

fof(f127,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f125])).

% (3431)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f125,plain,
    ( spl5_5
  <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f171,plain,(
    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f133,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f133,plain,(
    r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f23,f87,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f87,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f25,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

fof(f23,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f147,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl5_6 ),
    inference(subsumption_resolution,[],[f141,f131])).

fof(f131,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_6
  <=> r1_tarski(k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f141,plain,(
    r1_tarski(k1_tarski(sK2),sK1) ),
    inference(resolution,[],[f63,f37])).

fof(f63,plain,(
    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f23,f41])).

fof(f132,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f123,f74,f129,f125])).

fof(f74,plain,
    ( spl5_1
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f123,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK1)
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f122,f76])).

fof(f76,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f122,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f121,f76])).

fof(f121,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1) ),
    inference(subsumption_resolution,[],[f120,f26])).

fof(f26,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f120,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f119,f25])).

fof(f119,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f118,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

% (3433)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f118,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f117,f28])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f117,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f114,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f114,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k6_domain_1(u1_struct_0(sK0),sK2)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(superposition,[],[f24,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(f24,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f85,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f82,f25])).

fof(f82,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f23,f80,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f80,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_2
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f81,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f72,f78,f74])).

fof(f72,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    inference(resolution,[],[f22,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f22,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.51  % (3424)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (3421)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (3421)Refutation not found, incomplete strategy% (3421)------------------------------
% 0.22/0.52  % (3421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3421)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3421)Memory used [KB]: 10746
% 0.22/0.52  % (3421)Time elapsed: 0.111 s
% 0.22/0.52  % (3421)------------------------------
% 0.22/0.52  % (3421)------------------------------
% 0.22/0.55  % (3440)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (3439)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (3436)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.56/0.57  % (3422)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.56/0.57  % (3442)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.56/0.57  % (3428)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.56/0.57  % (3442)Refutation not found, incomplete strategy% (3442)------------------------------
% 1.56/0.57  % (3442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (3442)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (3442)Memory used [KB]: 10746
% 1.56/0.57  % (3442)Time elapsed: 0.150 s
% 1.56/0.57  % (3442)------------------------------
% 1.56/0.57  % (3442)------------------------------
% 1.56/0.57  % (3420)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.56/0.57  % (3444)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.56/0.57  % (3449)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.56/0.57  % (3438)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.56/0.57  % (3428)Refutation found. Thanks to Tanya!
% 1.56/0.57  % SZS status Theorem for theBenchmark
% 1.56/0.57  % (3434)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.56/0.57  % (3427)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.56/0.57  % (3430)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.56/0.58  % (3447)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.56/0.58  % (3419)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.56/0.58  % SZS output start Proof for theBenchmark
% 1.56/0.58  fof(f177,plain,(
% 1.56/0.58    $false),
% 1.56/0.58    inference(avatar_sat_refutation,[],[f81,f85,f132,f147,f176])).
% 1.56/0.58  fof(f176,plain,(
% 1.56/0.58    spl5_5),
% 1.56/0.58    inference(avatar_contradiction_clause,[],[f175])).
% 1.56/0.58  fof(f175,plain,(
% 1.56/0.58    $false | spl5_5),
% 1.56/0.58    inference(subsumption_resolution,[],[f171,f127])).
% 1.56/0.58  fof(f127,plain,(
% 1.56/0.58    ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_5),
% 1.56/0.58    inference(avatar_component_clause,[],[f125])).
% 1.56/0.58  % (3431)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.58  fof(f125,plain,(
% 1.56/0.58    spl5_5 <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.56/0.58  fof(f171,plain,(
% 1.56/0.58    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.58    inference(resolution,[],[f133,f41])).
% 1.56/0.58  fof(f41,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 1.56/0.58    inference(cnf_transformation,[],[f20])).
% 1.56/0.58  fof(f20,plain,(
% 1.56/0.58    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.56/0.58    inference(ennf_transformation,[],[f5])).
% 1.56/0.58  fof(f5,axiom,(
% 1.56/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 1.56/0.58  fof(f133,plain,(
% 1.56/0.58    r2_hidden(sK2,u1_struct_0(sK0))),
% 1.56/0.58    inference(unit_resulting_resolution,[],[f23,f87,f38])).
% 1.56/0.58  fof(f38,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f19])).
% 1.56/0.58  fof(f19,plain,(
% 1.56/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f1])).
% 1.56/0.58  fof(f1,axiom,(
% 1.56/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.56/0.58  fof(f87,plain,(
% 1.56/0.58    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.56/0.58    inference(unit_resulting_resolution,[],[f25,f37])).
% 1.56/0.58  fof(f37,plain,(
% 1.56/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.56/0.58    inference(cnf_transformation,[],[f6])).
% 1.56/0.58  fof(f6,axiom,(
% 1.56/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.56/0.58  fof(f25,plain,(
% 1.56/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.58    inference(cnf_transformation,[],[f13])).
% 1.56/0.58  fof(f13,plain,(
% 1.56/0.58    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.56/0.58    inference(flattening,[],[f12])).
% 1.56/0.58  fof(f12,plain,(
% 1.56/0.58    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f11])).
% 1.56/0.58  fof(f11,negated_conjecture,(
% 1.56/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 1.56/0.58    inference(negated_conjecture,[],[f10])).
% 1.56/0.58  fof(f10,conjecture,(
% 1.56/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).
% 1.56/0.58  fof(f23,plain,(
% 1.56/0.58    r2_hidden(sK2,sK1)),
% 1.56/0.58    inference(cnf_transformation,[],[f13])).
% 1.56/0.58  fof(f147,plain,(
% 1.56/0.58    spl5_6),
% 1.56/0.58    inference(avatar_contradiction_clause,[],[f146])).
% 1.56/0.58  fof(f146,plain,(
% 1.56/0.58    $false | spl5_6),
% 1.56/0.58    inference(subsumption_resolution,[],[f141,f131])).
% 1.56/0.58  fof(f131,plain,(
% 1.56/0.58    ~r1_tarski(k1_tarski(sK2),sK1) | spl5_6),
% 1.56/0.58    inference(avatar_component_clause,[],[f129])).
% 1.56/0.58  fof(f129,plain,(
% 1.56/0.58    spl5_6 <=> r1_tarski(k1_tarski(sK2),sK1)),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.56/0.58  fof(f141,plain,(
% 1.56/0.58    r1_tarski(k1_tarski(sK2),sK1)),
% 1.56/0.58    inference(resolution,[],[f63,f37])).
% 1.56/0.58  fof(f63,plain,(
% 1.56/0.58    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK1))),
% 1.56/0.58    inference(unit_resulting_resolution,[],[f23,f41])).
% 1.56/0.58  fof(f132,plain,(
% 1.56/0.58    ~spl5_5 | ~spl5_6 | ~spl5_1),
% 1.56/0.58    inference(avatar_split_clause,[],[f123,f74,f129,f125])).
% 1.56/0.58  fof(f74,plain,(
% 1.56/0.58    spl5_1 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.56/0.58  fof(f123,plain,(
% 1.56/0.58    ~r1_tarski(k1_tarski(sK2),sK1) | ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_1),
% 1.56/0.58    inference(forward_demodulation,[],[f122,f76])).
% 1.56/0.58  fof(f76,plain,(
% 1.56/0.58    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | ~spl5_1),
% 1.56/0.58    inference(avatar_component_clause,[],[f74])).
% 1.56/0.58  fof(f122,plain,(
% 1.56/0.58    ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1) | ~spl5_1),
% 1.56/0.58    inference(forward_demodulation,[],[f121,f76])).
% 1.56/0.58  fof(f121,plain,(
% 1.56/0.58    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1)),
% 1.56/0.58    inference(subsumption_resolution,[],[f120,f26])).
% 1.56/0.58  fof(f26,plain,(
% 1.56/0.58    v2_tex_2(sK1,sK0)),
% 1.56/0.58    inference(cnf_transformation,[],[f13])).
% 1.56/0.58  fof(f120,plain,(
% 1.56/0.58    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1) | ~v2_tex_2(sK1,sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f119,f25])).
% 1.56/0.58  fof(f119,plain,(
% 1.56/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1) | ~v2_tex_2(sK1,sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f118,f29])).
% 1.56/0.58  fof(f29,plain,(
% 1.56/0.58    l1_pre_topc(sK0)),
% 1.56/0.58    inference(cnf_transformation,[],[f13])).
% 1.56/0.58  % (3433)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.56/0.58  fof(f118,plain,(
% 1.56/0.58    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1) | ~v2_tex_2(sK1,sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f117,f28])).
% 1.56/0.58  fof(f28,plain,(
% 1.56/0.58    v2_pre_topc(sK0)),
% 1.56/0.58    inference(cnf_transformation,[],[f13])).
% 1.56/0.58  fof(f117,plain,(
% 1.56/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1) | ~v2_tex_2(sK1,sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f114,f27])).
% 1.56/0.58  fof(f27,plain,(
% 1.56/0.58    ~v2_struct_0(sK0)),
% 1.56/0.58    inference(cnf_transformation,[],[f13])).
% 1.56/0.58  fof(f114,plain,(
% 1.56/0.58    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1) | ~v2_tex_2(sK1,sK0)),
% 1.56/0.58    inference(trivial_inequality_removal,[],[f113])).
% 1.56/0.58  fof(f113,plain,(
% 1.56/0.58    k6_domain_1(u1_struct_0(sK0),sK2) != k6_domain_1(u1_struct_0(sK0),sK2) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK2),sK1) | ~v2_tex_2(sK1,sK0)),
% 1.56/0.58    inference(superposition,[],[f24,f31])).
% 1.56/0.58  fof(f31,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~v2_tex_2(X1,X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f16])).
% 1.56/0.58  fof(f16,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.56/0.58    inference(flattening,[],[f15])).
% 1.56/0.58  fof(f15,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f9])).
% 1.56/0.58  fof(f9,axiom,(
% 1.56/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).
% 1.56/0.58  fof(f24,plain,(
% 1.56/0.58    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 1.56/0.58    inference(cnf_transformation,[],[f13])).
% 1.73/0.58  fof(f85,plain,(
% 1.73/0.58    ~spl5_2),
% 1.73/0.58    inference(avatar_contradiction_clause,[],[f84])).
% 1.73/0.58  fof(f84,plain,(
% 1.73/0.58    $false | ~spl5_2),
% 1.73/0.58    inference(subsumption_resolution,[],[f82,f25])).
% 1.73/0.58  fof(f82,plain,(
% 1.73/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_2),
% 1.73/0.58    inference(unit_resulting_resolution,[],[f23,f80,f42])).
% 1.73/0.58  fof(f42,plain,(
% 1.73/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f21])).
% 1.73/0.58  fof(f21,plain,(
% 1.73/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.73/0.58    inference(ennf_transformation,[],[f7])).
% 1.73/0.58  fof(f7,axiom,(
% 1.73/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.73/0.58  fof(f80,plain,(
% 1.73/0.58    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_2),
% 1.73/0.58    inference(avatar_component_clause,[],[f78])).
% 1.73/0.58  fof(f78,plain,(
% 1.73/0.58    spl5_2 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.73/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.73/0.58  fof(f81,plain,(
% 1.73/0.58    spl5_1 | spl5_2),
% 1.73/0.58    inference(avatar_split_clause,[],[f72,f78,f74])).
% 1.73/0.58  fof(f72,plain,(
% 1.73/0.58    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)),
% 1.73/0.58    inference(resolution,[],[f22,f35])).
% 1.73/0.58  fof(f35,plain,(
% 1.73/0.58    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f18])).
% 1.73/0.58  fof(f18,plain,(
% 1.73/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.73/0.58    inference(flattening,[],[f17])).
% 1.73/0.58  fof(f17,plain,(
% 1.73/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.73/0.58    inference(ennf_transformation,[],[f8])).
% 1.73/0.58  fof(f8,axiom,(
% 1.73/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.73/0.58  fof(f22,plain,(
% 1.73/0.58    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.73/0.58    inference(cnf_transformation,[],[f13])).
% 1.73/0.58  % SZS output end Proof for theBenchmark
% 1.73/0.58  % (3428)------------------------------
% 1.73/0.58  % (3428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.58  % (3428)Termination reason: Refutation
% 1.73/0.58  
% 1.73/0.58  % (3428)Memory used [KB]: 10746
% 1.73/0.58  % (3428)Time elapsed: 0.135 s
% 1.73/0.58  % (3428)------------------------------
% 1.73/0.58  % (3428)------------------------------
% 1.73/0.58  % (3414)Success in time 0.226 s
%------------------------------------------------------------------------------
