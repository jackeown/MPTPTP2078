%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:34 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 142 expanded)
%              Number of leaves         :   16 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  174 ( 375 expanded)
%              Number of equality atoms :   48 (  80 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f350,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f211,f232,f349])).

fof(f349,plain,
    ( spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | spl4_2
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f47,f270,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) = X1 ) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f270,plain,
    ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
    | spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f146,f206])).

fof(f206,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f146,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f39,f143,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f143,plain,
    ( ~ v1_xboole_0(sK2)
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f139,f50,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f30,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f139,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f92,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f92,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f47,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f232,plain,
    ( spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f30,f92,f215,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f215,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f158,f210])).

fof(f210,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl4_4
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f158,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | spl4_2 ),
    inference(backward_demodulation,[],[f31,f157])).

fof(f157,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | spl4_2 ),
    inference(forward_demodulation,[],[f151,f65])).

fof(f65,plain,(
    k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f32,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f151,plain,
    ( k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f92,f32,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f31,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f211,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f59,f208,f204])).

fof(f59,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f57,f53])).

fof(f53,plain,(
    k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f29,f41])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    inference(resolution,[],[f29,f34])).

fof(f135,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f54,f126,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f126,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f96,f114])).

fof(f114,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f97,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f32,f93])).

fof(f93,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f96,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f31,f93])).

fof(f54,plain,(
    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f29,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:56:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (7130)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (7139)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.51  % (7125)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (7126)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (7130)Refutation not found, incomplete strategy% (7130)------------------------------
% 0.22/0.52  % (7130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7130)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7130)Memory used [KB]: 10746
% 0.22/0.52  % (7130)Time elapsed: 0.103 s
% 0.22/0.52  % (7130)------------------------------
% 0.22/0.52  % (7130)------------------------------
% 0.22/0.52  % (7127)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (7131)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (7137)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.53  % (7140)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.27/0.53  % (7140)Refutation not found, incomplete strategy% (7140)------------------------------
% 1.27/0.53  % (7140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (7140)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (7140)Memory used [KB]: 10618
% 1.27/0.53  % (7140)Time elapsed: 0.133 s
% 1.27/0.53  % (7140)------------------------------
% 1.27/0.53  % (7140)------------------------------
% 1.27/0.54  % (7144)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.27/0.54  % (7146)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.54  % (7147)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.27/0.54  % (7128)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.54  % (7124)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.54  % (7126)Refutation found. Thanks to Tanya!
% 1.27/0.54  % SZS status Theorem for theBenchmark
% 1.27/0.54  % SZS output start Proof for theBenchmark
% 1.27/0.54  fof(f350,plain,(
% 1.27/0.54    $false),
% 1.27/0.54    inference(avatar_sat_refutation,[],[f135,f211,f232,f349])).
% 1.27/0.54  fof(f349,plain,(
% 1.27/0.54    spl4_2 | ~spl4_3),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f347])).
% 1.27/0.54  fof(f347,plain,(
% 1.27/0.54    $false | (spl4_2 | ~spl4_3)),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f47,f270,f48])).
% 1.27/0.54  fof(f48,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) = X1) )),
% 1.27/0.54    inference(definition_unfolding,[],[f45,f46])).
% 1.27/0.54  fof(f46,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f3])).
% 1.27/0.54  fof(f3,axiom,(
% 1.27/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.27/0.54  fof(f45,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 1.27/0.54    inference(cnf_transformation,[],[f28])).
% 1.27/0.54  fof(f28,plain,(
% 1.27/0.54    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f4])).
% 1.27/0.54  fof(f4,axiom,(
% 1.27/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 1.27/0.54  fof(f270,plain,(
% 1.27/0.54    r2_hidden(sK3(k1_xboole_0),k1_xboole_0) | (spl4_2 | ~spl4_3)),
% 1.27/0.54    inference(backward_demodulation,[],[f146,f206])).
% 1.27/0.54  fof(f206,plain,(
% 1.27/0.54    k1_xboole_0 = sK2 | ~spl4_3),
% 1.27/0.54    inference(avatar_component_clause,[],[f204])).
% 1.27/0.54  fof(f204,plain,(
% 1.27/0.54    spl4_3 <=> k1_xboole_0 = sK2),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.27/0.54  fof(f146,plain,(
% 1.27/0.54    r2_hidden(sK3(sK2),sK2) | spl4_2),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f39,f143,f44])).
% 1.27/0.54  fof(f44,plain,(
% 1.27/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f27])).
% 1.27/0.54  fof(f27,plain,(
% 1.27/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.27/0.54    inference(flattening,[],[f26])).
% 1.27/0.54  fof(f26,plain,(
% 1.27/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f12])).
% 1.27/0.54  fof(f12,axiom,(
% 1.27/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.27/0.54  fof(f143,plain,(
% 1.27/0.54    ~v1_xboole_0(sK2) | spl4_2),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f139,f50,f40])).
% 1.27/0.54  fof(f40,plain,(
% 1.27/0.54    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f23])).
% 1.27/0.54  fof(f23,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f7])).
% 1.27/0.54  fof(f7,axiom,(
% 1.27/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.27/0.54  fof(f50,plain,(
% 1.27/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK2))),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f30,f36])).
% 1.27/0.54  fof(f36,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f13])).
% 1.27/0.54  fof(f13,axiom,(
% 1.27/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.27/0.54  fof(f30,plain,(
% 1.27/0.54    r1_tarski(sK1,sK2)),
% 1.27/0.54    inference(cnf_transformation,[],[f18])).
% 1.27/0.54  fof(f18,plain,(
% 1.27/0.54    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.27/0.54    inference(flattening,[],[f17])).
% 1.27/0.54  fof(f17,plain,(
% 1.27/0.54    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.27/0.54    inference(ennf_transformation,[],[f16])).
% 1.27/0.54  fof(f16,negated_conjecture,(
% 1.27/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.27/0.54    inference(negated_conjecture,[],[f15])).
% 1.27/0.54  fof(f15,conjecture,(
% 1.27/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 1.27/0.54  fof(f139,plain,(
% 1.27/0.54    ~v1_xboole_0(sK1) | spl4_2),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f92,f43])).
% 1.27/0.54  fof(f43,plain,(
% 1.27/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f25])).
% 1.27/0.54  fof(f25,plain,(
% 1.27/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f1])).
% 1.27/0.54  fof(f1,axiom,(
% 1.27/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.27/0.54  fof(f92,plain,(
% 1.27/0.54    k1_xboole_0 != sK1 | spl4_2),
% 1.27/0.54    inference(avatar_component_clause,[],[f91])).
% 1.27/0.54  fof(f91,plain,(
% 1.27/0.54    spl4_2 <=> k1_xboole_0 = sK1),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.27/0.54  fof(f39,plain,(
% 1.27/0.54    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f6])).
% 1.27/0.54  fof(f6,axiom,(
% 1.27/0.54    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.27/0.54  fof(f47,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0)))) )),
% 1.27/0.54    inference(definition_unfolding,[],[f42,f46])).
% 1.27/0.54  fof(f42,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f5])).
% 1.27/0.54  fof(f5,axiom,(
% 1.27/0.54    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.27/0.54  fof(f232,plain,(
% 1.27/0.54    spl4_2 | ~spl4_4),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f226])).
% 1.27/0.54  fof(f226,plain,(
% 1.27/0.54    $false | (spl4_2 | ~spl4_4)),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f30,f92,f215,f38])).
% 1.27/0.54  fof(f38,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f22])).
% 1.27/0.54  fof(f22,plain,(
% 1.27/0.54    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.27/0.54    inference(flattening,[],[f21])).
% 1.27/0.54  fof(f21,plain,(
% 1.27/0.54    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f14])).
% 1.27/0.54  fof(f14,axiom,(
% 1.27/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 1.27/0.54  fof(f215,plain,(
% 1.27/0.54    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (spl4_2 | ~spl4_4)),
% 1.27/0.54    inference(backward_demodulation,[],[f158,f210])).
% 1.27/0.54  fof(f210,plain,(
% 1.27/0.54    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl4_4),
% 1.27/0.54    inference(avatar_component_clause,[],[f208])).
% 1.27/0.54  fof(f208,plain,(
% 1.27/0.54    spl4_4 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.27/0.54  fof(f158,plain,(
% 1.27/0.54    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | spl4_2),
% 1.27/0.54    inference(backward_demodulation,[],[f31,f157])).
% 1.27/0.54  fof(f157,plain,(
% 1.27/0.54    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | spl4_2),
% 1.27/0.54    inference(forward_demodulation,[],[f151,f65])).
% 1.27/0.54  fof(f65,plain,(
% 1.27/0.54    k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1)),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f32,f41])).
% 1.27/0.54  fof(f41,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f24])).
% 1.27/0.54  fof(f24,plain,(
% 1.27/0.54    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.27/0.54    inference(ennf_transformation,[],[f10])).
% 1.27/0.54  fof(f10,axiom,(
% 1.27/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 1.27/0.54  fof(f32,plain,(
% 1.27/0.54    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.27/0.54    inference(cnf_transformation,[],[f18])).
% 1.27/0.54  fof(f151,plain,(
% 1.27/0.54    k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) | spl4_2),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f92,f32,f34])).
% 1.27/0.54  fof(f34,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f19])).
% 1.27/0.54  fof(f19,plain,(
% 1.27/0.54    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.27/0.54    inference(ennf_transformation,[],[f8])).
% 1.27/0.54  fof(f8,axiom,(
% 1.27/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 1.27/0.54  fof(f31,plain,(
% 1.27/0.54    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 1.27/0.54    inference(cnf_transformation,[],[f18])).
% 1.27/0.54  fof(f211,plain,(
% 1.27/0.54    spl4_3 | spl4_4),
% 1.27/0.54    inference(avatar_split_clause,[],[f59,f208,f204])).
% 1.27/0.54  fof(f59,plain,(
% 1.27/0.54    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2),
% 1.27/0.54    inference(forward_demodulation,[],[f57,f53])).
% 1.27/0.54  fof(f53,plain,(
% 1.27/0.54    k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2)),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f29,f41])).
% 1.27/0.54  fof(f29,plain,(
% 1.27/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.27/0.54    inference(cnf_transformation,[],[f18])).
% 1.27/0.54  fof(f57,plain,(
% 1.27/0.54    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 1.27/0.54    inference(resolution,[],[f29,f34])).
% 1.27/0.54  fof(f135,plain,(
% 1.27/0.54    ~spl4_2),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f131])).
% 1.27/0.54  fof(f131,plain,(
% 1.27/0.54    $false | ~spl4_2),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f54,f126,f37])).
% 1.27/0.54  fof(f37,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f13])).
% 1.27/0.54  fof(f126,plain,(
% 1.27/0.54    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~spl4_2),
% 1.27/0.54    inference(backward_demodulation,[],[f96,f114])).
% 1.27/0.54  fof(f114,plain,(
% 1.27/0.54    sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~spl4_2),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f97,f49])).
% 1.27/0.54  fof(f49,plain,(
% 1.27/0.54    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 1.27/0.54    inference(equality_resolution,[],[f33])).
% 1.27/0.54  fof(f33,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f19])).
% 1.27/0.54  fof(f97,plain,(
% 1.27/0.54    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_2),
% 1.27/0.54    inference(backward_demodulation,[],[f32,f93])).
% 1.27/0.54  fof(f93,plain,(
% 1.27/0.54    k1_xboole_0 = sK1 | ~spl4_2),
% 1.27/0.54    inference(avatar_component_clause,[],[f91])).
% 1.27/0.54  fof(f96,plain,(
% 1.27/0.54    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | ~spl4_2),
% 1.27/0.54    inference(backward_demodulation,[],[f31,f93])).
% 1.27/0.54  fof(f54,plain,(
% 1.27/0.54    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f29,f35])).
% 1.27/0.54  fof(f35,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f20])).
% 1.27/0.54  fof(f20,plain,(
% 1.27/0.54    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.27/0.54    inference(ennf_transformation,[],[f9])).
% 1.27/0.54  fof(f9,axiom,(
% 1.27/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 1.27/0.54  % SZS output end Proof for theBenchmark
% 1.27/0.54  % (7126)------------------------------
% 1.27/0.54  % (7126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (7126)Termination reason: Refutation
% 1.27/0.54  
% 1.27/0.54  % (7126)Memory used [KB]: 6268
% 1.27/0.54  % (7126)Time elapsed: 0.130 s
% 1.27/0.54  % (7126)------------------------------
% 1.27/0.54  % (7126)------------------------------
% 1.27/0.54  % (7119)Success in time 0.178 s
%------------------------------------------------------------------------------
