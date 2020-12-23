%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:43 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 136 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  165 ( 356 expanded)
%              Number of equality atoms :   25 (  61 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f89,f127,f172,f175])).

fof(f175,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f173,f100])).

fof(f100,plain,(
    r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(resolution,[],[f98,f26])).

fof(f26,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

% (21471)Refutation not found, incomplete strategy% (21471)------------------------------
% (21471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21471)Termination reason: Refutation not found, incomplete strategy

% (21471)Memory used [KB]: 10618
% (21471)Time elapsed: 0.090 s
% (21471)------------------------------
% (21471)------------------------------
fof(f98,plain,(
    ! [X5] :
      ( ~ r1_tarski(k6_relat_1(X5),sK2)
      | r1_tarski(X5,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f94,f55])).

fof(f55,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f54,f25])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_relat_1(X2) ) ),
    inference(resolution,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(X0,k1_relat_1(X1))
      | ~ r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f92,f27])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f30,f28])).

fof(f28,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f173,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | spl3_2 ),
    inference(forward_demodulation,[],[f51,f168])).

fof(f168,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f39,f25])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f51,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_2
  <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f172,plain,
    ( spl3_1
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl3_1
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f170,f47])).

fof(f47,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_1
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f170,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f169,f84])).

fof(f84,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_5
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f169,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f40,f25])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f127,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f125,f88])).

fof(f88,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_6
  <=> r1_tarski(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f125,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f123,f26])).

fof(f123,plain,(
    ! [X5] :
      ( ~ r1_tarski(k6_relat_1(X5),sK2)
      | r1_tarski(X5,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f119,f55])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(X0,k2_relat_1(X1))
      | ~ r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f117,f27])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f31,f29])).

fof(f29,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f80,f86,f82])).

fof(f80,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f79,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f79,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f78,f63])).

fof(f63,plain,(
    ! [X5] :
      ( ~ v5_relat_1(sK2,X5)
      | r1_tarski(k2_relat_1(sK2),X5) ) ),
    inference(resolution,[],[f35,f55])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f78,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f41,f25])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f52,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f49,f45])).

fof(f24,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 15:33:03 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.48  % (21477)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.18/0.48  % (21477)Refutation not found, incomplete strategy% (21477)------------------------------
% 0.18/0.48  % (21477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (21493)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.18/0.48  % (21477)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.48  
% 0.18/0.48  % (21477)Memory used [KB]: 10618
% 0.18/0.48  % (21477)Time elapsed: 0.065 s
% 0.18/0.48  % (21477)------------------------------
% 0.18/0.48  % (21477)------------------------------
% 0.18/0.49  % (21470)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.18/0.49  % (21492)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.18/0.49  % (21471)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.49  % (21470)Refutation not found, incomplete strategy% (21470)------------------------------
% 0.18/0.49  % (21470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (21470)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (21470)Memory used [KB]: 10618
% 0.18/0.49  % (21470)Time elapsed: 0.091 s
% 0.18/0.49  % (21470)------------------------------
% 0.18/0.49  % (21470)------------------------------
% 0.18/0.49  % (21493)Refutation found. Thanks to Tanya!
% 0.18/0.49  % SZS status Theorem for theBenchmark
% 0.18/0.49  % SZS output start Proof for theBenchmark
% 0.18/0.49  fof(f176,plain,(
% 0.18/0.49    $false),
% 0.18/0.49    inference(avatar_sat_refutation,[],[f52,f89,f127,f172,f175])).
% 0.18/0.49  fof(f175,plain,(
% 0.18/0.49    spl3_2),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f174])).
% 0.18/0.49  fof(f174,plain,(
% 0.18/0.49    $false | spl3_2),
% 0.18/0.49    inference(subsumption_resolution,[],[f173,f100])).
% 0.18/0.49  fof(f100,plain,(
% 0.18/0.49    r1_tarski(sK1,k1_relat_1(sK2))),
% 0.18/0.49    inference(resolution,[],[f98,f26])).
% 0.18/0.49  fof(f26,plain,(
% 0.18/0.49    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.18/0.49    inference(cnf_transformation,[],[f16])).
% 0.18/0.49  fof(f16,plain,(
% 0.18/0.49    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.49    inference(flattening,[],[f15])).
% 0.18/0.49  fof(f15,plain,(
% 0.18/0.49    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.49    inference(ennf_transformation,[],[f12])).
% 0.18/0.49  fof(f12,negated_conjecture,(
% 0.18/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.18/0.49    inference(negated_conjecture,[],[f11])).
% 0.18/0.49  fof(f11,conjecture,(
% 0.18/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).
% 0.18/0.49  % (21471)Refutation not found, incomplete strategy% (21471)------------------------------
% 0.18/0.49  % (21471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (21471)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (21471)Memory used [KB]: 10618
% 0.18/0.49  % (21471)Time elapsed: 0.090 s
% 0.18/0.49  % (21471)------------------------------
% 0.18/0.49  % (21471)------------------------------
% 0.18/0.49  fof(f98,plain,(
% 0.18/0.49    ( ! [X5] : (~r1_tarski(k6_relat_1(X5),sK2) | r1_tarski(X5,k1_relat_1(sK2))) )),
% 0.18/0.49    inference(resolution,[],[f94,f55])).
% 0.18/0.49  fof(f55,plain,(
% 0.18/0.49    v1_relat_1(sK2)),
% 0.18/0.49    inference(resolution,[],[f54,f25])).
% 0.18/0.49  fof(f25,plain,(
% 0.18/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.49    inference(cnf_transformation,[],[f16])).
% 0.18/0.49  fof(f54,plain,(
% 0.18/0.49    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_relat_1(X2)) )),
% 0.18/0.49    inference(resolution,[],[f32,f33])).
% 0.18/0.49  fof(f33,plain,(
% 0.18/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f4])).
% 0.18/0.49  fof(f4,axiom,(
% 0.18/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.18/0.49  fof(f32,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f19])).
% 0.18/0.49  fof(f19,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.18/0.49    inference(ennf_transformation,[],[f2])).
% 0.18/0.49  fof(f2,axiom,(
% 0.18/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.18/0.49  fof(f94,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(X0,k1_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1)) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f92,f27])).
% 0.18/0.49  fof(f27,plain,(
% 0.18/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f14])).
% 0.18/0.49  fof(f14,plain,(
% 0.18/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.18/0.49    inference(pure_predicate_removal,[],[f7])).
% 0.18/0.49  fof(f7,axiom,(
% 0.18/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.18/0.49  fof(f92,plain,(
% 0.18/0.49    ( ! [X0,X1] : (r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.18/0.49    inference(superposition,[],[f30,f28])).
% 0.18/0.49  fof(f28,plain,(
% 0.18/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f6])).
% 0.18/0.49  fof(f6,axiom,(
% 0.18/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.18/0.49  fof(f30,plain,(
% 0.18/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f18])).
% 0.18/0.49  fof(f18,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.18/0.49    inference(flattening,[],[f17])).
% 0.18/0.49  fof(f17,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.18/0.49    inference(ennf_transformation,[],[f5])).
% 0.18/0.49  fof(f5,axiom,(
% 0.18/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.18/0.49  fof(f173,plain,(
% 0.18/0.49    ~r1_tarski(sK1,k1_relat_1(sK2)) | spl3_2),
% 0.18/0.49    inference(forward_demodulation,[],[f51,f168])).
% 0.18/0.49  fof(f168,plain,(
% 0.18/0.49    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.18/0.49    inference(resolution,[],[f39,f25])).
% 0.18/0.49  fof(f39,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f21])).
% 0.18/0.49  fof(f21,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.49    inference(ennf_transformation,[],[f9])).
% 0.18/0.49  fof(f9,axiom,(
% 0.18/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.18/0.49  fof(f51,plain,(
% 0.18/0.49    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | spl3_2),
% 0.18/0.49    inference(avatar_component_clause,[],[f49])).
% 0.18/0.49  fof(f49,plain,(
% 0.18/0.49    spl3_2 <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.18/0.49  fof(f172,plain,(
% 0.18/0.49    spl3_1 | ~spl3_5),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f171])).
% 0.18/0.49  fof(f171,plain,(
% 0.18/0.49    $false | (spl3_1 | ~spl3_5)),
% 0.18/0.49    inference(subsumption_resolution,[],[f170,f47])).
% 0.18/0.49  fof(f47,plain,(
% 0.18/0.49    sK1 != k2_relset_1(sK0,sK1,sK2) | spl3_1),
% 0.18/0.49    inference(avatar_component_clause,[],[f45])).
% 0.18/0.49  fof(f45,plain,(
% 0.18/0.49    spl3_1 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.18/0.49  fof(f170,plain,(
% 0.18/0.49    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_5),
% 0.18/0.49    inference(forward_demodulation,[],[f169,f84])).
% 0.18/0.49  fof(f84,plain,(
% 0.18/0.49    sK1 = k2_relat_1(sK2) | ~spl3_5),
% 0.18/0.49    inference(avatar_component_clause,[],[f82])).
% 0.18/0.49  fof(f82,plain,(
% 0.18/0.49    spl3_5 <=> sK1 = k2_relat_1(sK2)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.18/0.49  fof(f169,plain,(
% 0.18/0.49    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.18/0.49    inference(resolution,[],[f40,f25])).
% 0.18/0.49  fof(f40,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f22])).
% 0.18/0.49  fof(f22,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.49    inference(ennf_transformation,[],[f10])).
% 0.18/0.49  fof(f10,axiom,(
% 0.18/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.18/0.49  fof(f127,plain,(
% 0.18/0.49    spl3_6),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f126])).
% 0.18/0.49  fof(f126,plain,(
% 0.18/0.49    $false | spl3_6),
% 0.18/0.49    inference(subsumption_resolution,[],[f125,f88])).
% 0.18/0.49  fof(f88,plain,(
% 0.18/0.49    ~r1_tarski(sK1,k2_relat_1(sK2)) | spl3_6),
% 0.18/0.49    inference(avatar_component_clause,[],[f86])).
% 0.18/0.49  fof(f86,plain,(
% 0.18/0.49    spl3_6 <=> r1_tarski(sK1,k2_relat_1(sK2))),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.18/0.49  fof(f125,plain,(
% 0.18/0.49    r1_tarski(sK1,k2_relat_1(sK2))),
% 0.18/0.49    inference(resolution,[],[f123,f26])).
% 0.18/0.49  fof(f123,plain,(
% 0.18/0.49    ( ! [X5] : (~r1_tarski(k6_relat_1(X5),sK2) | r1_tarski(X5,k2_relat_1(sK2))) )),
% 0.18/0.49    inference(resolution,[],[f119,f55])).
% 0.18/0.49  fof(f119,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(X0,k2_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1)) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f117,f27])).
% 0.18/0.49  fof(f117,plain,(
% 0.18/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.18/0.49    inference(superposition,[],[f31,f29])).
% 0.18/0.49  fof(f29,plain,(
% 0.18/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f6])).
% 0.18/0.49  fof(f31,plain,(
% 0.18/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f18])).
% 0.18/0.49  fof(f89,plain,(
% 0.18/0.49    spl3_5 | ~spl3_6),
% 0.18/0.49    inference(avatar_split_clause,[],[f80,f86,f82])).
% 0.18/0.49  fof(f80,plain,(
% 0.18/0.49    ~r1_tarski(sK1,k2_relat_1(sK2)) | sK1 = k2_relat_1(sK2)),
% 0.18/0.49    inference(resolution,[],[f79,f38])).
% 0.18/0.49  fof(f38,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.18/0.49    inference(cnf_transformation,[],[f1])).
% 0.18/0.49  fof(f1,axiom,(
% 0.18/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.18/0.49  fof(f79,plain,(
% 0.18/0.49    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.18/0.49    inference(resolution,[],[f78,f63])).
% 0.18/0.49  fof(f63,plain,(
% 0.18/0.49    ( ! [X5] : (~v5_relat_1(sK2,X5) | r1_tarski(k2_relat_1(sK2),X5)) )),
% 0.18/0.49    inference(resolution,[],[f35,f55])).
% 0.18/0.49  fof(f35,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f20])).
% 0.18/0.49  fof(f20,plain,(
% 0.18/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.18/0.49    inference(ennf_transformation,[],[f3])).
% 0.18/0.49  fof(f3,axiom,(
% 0.18/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.18/0.49  fof(f78,plain,(
% 0.18/0.49    v5_relat_1(sK2,sK1)),
% 0.18/0.49    inference(resolution,[],[f41,f25])).
% 0.18/0.49  fof(f41,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f23])).
% 0.18/0.49  fof(f23,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.49    inference(ennf_transformation,[],[f13])).
% 0.18/0.49  fof(f13,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.18/0.49    inference(pure_predicate_removal,[],[f8])).
% 0.18/0.49  fof(f8,axiom,(
% 0.18/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.18/0.49  fof(f52,plain,(
% 0.18/0.49    ~spl3_1 | ~spl3_2),
% 0.18/0.49    inference(avatar_split_clause,[],[f24,f49,f45])).
% 0.18/0.49  fof(f24,plain,(
% 0.18/0.49    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.18/0.49    inference(cnf_transformation,[],[f16])).
% 0.18/0.49  % SZS output end Proof for theBenchmark
% 0.18/0.49  % (21493)------------------------------
% 0.18/0.49  % (21493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (21493)Termination reason: Refutation
% 0.18/0.49  
% 0.18/0.49  % (21493)Memory used [KB]: 10618
% 0.18/0.49  % (21493)Time elapsed: 0.070 s
% 0.18/0.49  % (21493)------------------------------
% 0.18/0.49  % (21493)------------------------------
% 0.18/0.49  % (21478)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.18/0.49  % (21479)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.18/0.49  % (21469)Success in time 0.152 s
%------------------------------------------------------------------------------
