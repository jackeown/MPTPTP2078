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
% DateTime   : Thu Dec  3 12:49:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 126 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  174 ( 387 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f118,f148,f152,f155,f163,f165,f173])).

fof(f173,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl4_16 ),
    inference(resolution,[],[f162,f19])).

fof(f19,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(f162,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl4_16
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f165,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl4_15 ),
    inference(resolution,[],[f159,f20])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f159,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl4_15
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f163,plain,
    ( ~ spl4_9
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_5
    | spl4_13 ),
    inference(avatar_split_clause,[],[f156,f143,f83,f161,f158,f107])).

fof(f107,plain,
    ( spl4_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f83,plain,
    ( spl4_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f143,plain,
    ( spl4_13
  <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f156,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r1_tarski(sK2,sK3)
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | spl4_13 ),
    inference(resolution,[],[f144,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

fof(f144,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f155,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl4_14 ),
    inference(resolution,[],[f153,f18])).

fof(f18,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f153,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_14 ),
    inference(resolution,[],[f147,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f32,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f25,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f147,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl4_14
  <=> v1_relat_1(k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f152,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl4_12 ),
    inference(resolution,[],[f149,f22])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f149,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_12 ),
    inference(resolution,[],[f141,f44])).

fof(f141,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl4_12
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f148,plain,
    ( ~ spl4_12
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f137,f146,f143,f140])).

fof(f137,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f58,f21])).

fof(f21,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK3,X0))
      | ~ v1_relat_1(k7_relat_1(sK3,X0))
      | ~ r1_tarski(k7_relat_1(sK2,X1),k7_relat_1(sK3,X0))
      | ~ v1_relat_1(k7_relat_1(sK2,X1)) ) ),
    inference(superposition,[],[f36,f33])).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f27,f18])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f36,plain,(
    ! [X2,X3] :
      ( r1_tarski(k9_relat_1(sK2,X2),k2_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(k7_relat_1(sK2,X2),X3)
      | ~ v1_relat_1(k7_relat_1(sK2,X2)) ) ),
    inference(superposition,[],[f24,f34])).

fof(f34,plain,(
    ! [X1] : k2_relat_1(k7_relat_1(sK2,X1)) = k9_relat_1(sK2,X1) ),
    inference(resolution,[],[f27,f22])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f118,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl4_9 ),
    inference(resolution,[],[f108,f22])).

fof(f108,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f91,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl4_5 ),
    inference(resolution,[],[f84,f18])).

fof(f84,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:32:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (18129)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.49  % (18121)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.49  % (18129)Refutation not found, incomplete strategy% (18129)------------------------------
% 0.21/0.49  % (18129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18121)Refutation not found, incomplete strategy% (18121)------------------------------
% 0.21/0.49  % (18121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18129)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (18129)Memory used [KB]: 1535
% 0.21/0.49  % (18129)Time elapsed: 0.079 s
% 0.21/0.49  % (18129)------------------------------
% 0.21/0.49  % (18129)------------------------------
% 0.21/0.50  % (18121)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (18121)Memory used [KB]: 10490
% 0.21/0.50  % (18121)Time elapsed: 0.081 s
% 0.21/0.50  % (18121)------------------------------
% 0.21/0.50  % (18121)------------------------------
% 0.21/0.50  % (18133)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (18117)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  % (18125)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (18125)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f91,f118,f148,f152,f155,f163,f165,f173])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    spl4_16),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f172])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    $false | spl4_16),
% 0.21/0.52    inference(resolution,[],[f162,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    r1_tarski(sK2,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f7])).
% 0.21/0.52  fof(f7,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    ~r1_tarski(sK2,sK3) | spl4_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f161])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    spl4_16 <=> r1_tarski(sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    spl4_15),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f164])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    $false | spl4_15),
% 0.21/0.52    inference(resolution,[],[f159,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    r1_tarski(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK1) | spl4_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f158])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    spl4_15 <=> r1_tarski(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    ~spl4_9 | ~spl4_15 | ~spl4_16 | ~spl4_5 | spl4_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f156,f143,f83,f161,f158,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    spl4_9 <=> v1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl4_5 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    spl4_13 <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | ~r1_tarski(sK2,sK3) | ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK2) | spl4_13),
% 0.21/0.52    inference(resolution,[],[f144,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | ~v1_relat_1(X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) | spl4_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f143])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    spl4_14),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f154])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    $false | spl4_14),
% 0.21/0.52    inference(resolution,[],[f153,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    v1_relat_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | spl4_14),
% 0.21/0.52    inference(resolution,[],[f147,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f32,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f25,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ~v1_relat_1(k7_relat_1(sK3,sK1)) | spl4_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f146])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    spl4_14 <=> v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    spl4_12),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    $false | spl4_12),
% 0.21/0.52    inference(resolution,[],[f149,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ~v1_relat_1(sK2) | spl4_12),
% 0.21/0.52    inference(resolution,[],[f141,f44])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl4_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f140])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    spl4_12 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ~spl4_12 | ~spl4_13 | ~spl4_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f137,f146,f143,f140])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.52    inference(resolution,[],[f58,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK3,X0)) | ~v1_relat_1(k7_relat_1(sK3,X0)) | ~r1_tarski(k7_relat_1(sK2,X1),k7_relat_1(sK3,X0)) | ~v1_relat_1(k7_relat_1(sK2,X1))) )),
% 0.21/0.52    inference(superposition,[],[f36,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0] : (k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0)) )),
% 0.21/0.52    inference(resolution,[],[f27,f18])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2,X3] : (r1_tarski(k9_relat_1(sK2,X2),k2_relat_1(X3)) | ~v1_relat_1(X3) | ~r1_tarski(k7_relat_1(sK2,X2),X3) | ~v1_relat_1(k7_relat_1(sK2,X2))) )),
% 0.21/0.52    inference(superposition,[],[f24,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X1] : (k2_relat_1(k7_relat_1(sK2,X1)) = k9_relat_1(sK2,X1)) )),
% 0.21/0.52    inference(resolution,[],[f27,f22])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl4_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    $false | spl4_9),
% 0.21/0.52    inference(resolution,[],[f108,f22])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ~v1_relat_1(sK2) | spl4_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f107])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl4_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    $false | spl4_5),
% 0.21/0.52    inference(resolution,[],[f84,f18])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f83])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (18125)------------------------------
% 0.21/0.52  % (18125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18125)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (18125)Memory used [KB]: 10746
% 0.21/0.52  % (18125)Time elapsed: 0.109 s
% 0.21/0.52  % (18125)------------------------------
% 0.21/0.52  % (18125)------------------------------
% 1.24/0.52  % (18135)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.24/0.52  % (18112)Success in time 0.154 s
%------------------------------------------------------------------------------
