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
% DateTime   : Thu Dec  3 13:03:39 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   98 ( 119 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f78])).

fof(f78,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f72,f76])).

% (8005)Refutation not found, incomplete strategy% (8005)------------------------------
% (8005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f76,plain,
    ( ! [X2,X0,X1] : k1_xboole_0 = k7_relset_1(X0,X1,k1_xboole_0,X2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f75,f58])).

fof(f58,plain,
    ( ! [X4] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X4)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f57,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f57,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,X4))
        | k1_xboole_0 = k9_relat_1(k1_xboole_0,X4) )
    | ~ spl3_2 ),
    inference(resolution,[],[f35,f48])).

fof(f48,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_2
  <=> ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f75,plain,(
    ! [X2,X0,X1] : k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
    inference(resolution,[],[f37,f29])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f72,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f24,f67])).

fof(f67,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f65,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f65,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f63,f23])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f32,f25])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f24,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f50,f45])).

fof(f45,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f36,f29])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f49,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f41,f47,f43])).

fof(f41,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f31,f27])).

fof(f27,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:37:01 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.45  % (8013)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.45  % (8021)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.18/0.45  % (8003)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.18/0.46  % (8021)Refutation found. Thanks to Tanya!
% 0.18/0.46  % SZS status Theorem for theBenchmark
% 0.18/0.46  % (7999)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.18/0.46  % (8005)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.18/0.47  % SZS output start Proof for theBenchmark
% 0.18/0.47  fof(f79,plain,(
% 0.18/0.47    $false),
% 0.18/0.47    inference(avatar_sat_refutation,[],[f49,f53,f78])).
% 0.18/0.47  fof(f78,plain,(
% 0.18/0.47    ~spl3_2),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f77])).
% 0.18/0.47  fof(f77,plain,(
% 0.18/0.47    $false | ~spl3_2),
% 0.18/0.47    inference(subsumption_resolution,[],[f72,f76])).
% 0.18/0.47  % (8005)Refutation not found, incomplete strategy% (8005)------------------------------
% 0.18/0.47  % (8005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  fof(f76,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relset_1(X0,X1,k1_xboole_0,X2)) ) | ~spl3_2),
% 0.18/0.47    inference(forward_demodulation,[],[f75,f58])).
% 0.18/0.47  fof(f58,plain,(
% 0.18/0.47    ( ! [X4] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X4)) ) | ~spl3_2),
% 0.18/0.47    inference(subsumption_resolution,[],[f57,f28])).
% 0.18/0.47  fof(f28,plain,(
% 0.18/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f4])).
% 0.18/0.47  fof(f4,axiom,(
% 0.18/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.18/0.47  fof(f57,plain,(
% 0.18/0.47    ( ! [X4] : (~r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,X4)) | k1_xboole_0 = k9_relat_1(k1_xboole_0,X4)) ) | ~spl3_2),
% 0.18/0.47    inference(resolution,[],[f35,f48])).
% 0.18/0.47  fof(f48,plain,(
% 0.18/0.47    ( ! [X0] : (r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl3_2),
% 0.18/0.47    inference(avatar_component_clause,[],[f47])).
% 0.18/0.47  fof(f47,plain,(
% 0.18/0.47    spl3_2 <=> ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.18/0.47  fof(f35,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.18/0.47    inference(cnf_transformation,[],[f3])).
% 0.18/0.47  fof(f3,axiom,(
% 0.18/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.18/0.47  fof(f75,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2)) )),
% 0.18/0.47    inference(resolution,[],[f37,f29])).
% 0.18/0.47  fof(f29,plain,(
% 0.18/0.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f5])).
% 0.18/0.47  fof(f5,axiom,(
% 0.18/0.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.18/0.47  fof(f37,plain,(
% 0.18/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f22])).
% 0.18/0.47  fof(f22,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(ennf_transformation,[],[f11])).
% 0.18/0.47  fof(f11,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.18/0.47  fof(f72,plain,(
% 0.18/0.47    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.18/0.47    inference(backward_demodulation,[],[f24,f67])).
% 0.18/0.47  fof(f67,plain,(
% 0.18/0.47    k1_xboole_0 = sK2),
% 0.18/0.47    inference(resolution,[],[f65,f30])).
% 0.18/0.47  fof(f30,plain,(
% 0.18/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.18/0.47    inference(cnf_transformation,[],[f18])).
% 0.18/0.47  fof(f18,plain,(
% 0.18/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.18/0.47    inference(ennf_transformation,[],[f2])).
% 0.18/0.47  fof(f2,axiom,(
% 0.18/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.18/0.47  fof(f65,plain,(
% 0.18/0.47    v1_xboole_0(sK2)),
% 0.18/0.47    inference(resolution,[],[f63,f23])).
% 0.18/0.47  fof(f23,plain,(
% 0.18/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.18/0.47    inference(cnf_transformation,[],[f17])).
% 0.18/0.47  fof(f17,plain,(
% 0.18/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.18/0.47    inference(ennf_transformation,[],[f15])).
% 0.18/0.47  fof(f15,plain,(
% 0.18/0.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.18/0.47    inference(pure_predicate_removal,[],[f14])).
% 0.18/0.47  fof(f14,plain,(
% 0.18/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.18/0.47    inference(pure_predicate_removal,[],[f13])).
% 0.18/0.47  fof(f13,negated_conjecture,(
% 0.18/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.18/0.47    inference(negated_conjecture,[],[f12])).
% 0.18/0.47  fof(f12,conjecture,(
% 0.18/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).
% 0.18/0.47  fof(f63,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) )),
% 0.18/0.47    inference(resolution,[],[f32,f25])).
% 0.18/0.47  fof(f25,plain,(
% 0.18/0.47    v1_xboole_0(k1_xboole_0)),
% 0.18/0.47    inference(cnf_transformation,[],[f1])).
% 0.18/0.47  fof(f1,axiom,(
% 0.18/0.47    v1_xboole_0(k1_xboole_0)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.18/0.47  fof(f32,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f20])).
% 0.18/0.47  fof(f20,plain,(
% 0.18/0.47    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.18/0.47    inference(ennf_transformation,[],[f10])).
% 0.18/0.47  fof(f10,axiom,(
% 0.18/0.47    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.18/0.47  fof(f24,plain,(
% 0.18/0.47    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.18/0.47    inference(cnf_transformation,[],[f17])).
% 0.18/0.47  fof(f53,plain,(
% 0.18/0.47    spl3_1),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f52])).
% 0.18/0.47  fof(f52,plain,(
% 0.18/0.47    $false | spl3_1),
% 0.18/0.47    inference(subsumption_resolution,[],[f50,f45])).
% 0.18/0.47  fof(f45,plain,(
% 0.18/0.47    ~v1_relat_1(k1_xboole_0) | spl3_1),
% 0.18/0.47    inference(avatar_component_clause,[],[f43])).
% 0.18/0.47  fof(f43,plain,(
% 0.18/0.47    spl3_1 <=> v1_relat_1(k1_xboole_0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.18/0.47  fof(f50,plain,(
% 0.18/0.47    v1_relat_1(k1_xboole_0)),
% 0.18/0.47    inference(resolution,[],[f36,f29])).
% 0.18/0.47  fof(f36,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f21])).
% 0.18/0.47  fof(f21,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(ennf_transformation,[],[f9])).
% 0.18/0.47  fof(f9,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.18/0.47  fof(f49,plain,(
% 0.18/0.47    ~spl3_1 | spl3_2),
% 0.18/0.47    inference(avatar_split_clause,[],[f41,f47,f43])).
% 0.18/0.47  fof(f41,plain,(
% 0.18/0.47    ( ! [X0] : (r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.18/0.47    inference(superposition,[],[f31,f27])).
% 0.18/0.47  fof(f27,plain,(
% 0.18/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.18/0.47    inference(cnf_transformation,[],[f8])).
% 0.18/0.47  fof(f8,axiom,(
% 0.18/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.18/0.47  fof(f31,plain,(
% 0.18/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f19])).
% 0.18/0.47  fof(f19,plain,(
% 0.18/0.47    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.18/0.47    inference(ennf_transformation,[],[f7])).
% 0.18/0.47  fof(f7,axiom,(
% 0.18/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 0.18/0.47  % SZS output end Proof for theBenchmark
% 0.18/0.47  % (8021)------------------------------
% 0.18/0.47  % (8021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (8021)Termination reason: Refutation
% 0.18/0.47  
% 0.18/0.47  % (8021)Memory used [KB]: 10618
% 0.18/0.47  % (8021)Time elapsed: 0.060 s
% 0.18/0.47  % (8021)------------------------------
% 0.18/0.47  % (8021)------------------------------
% 0.18/0.47  % (7998)Success in time 0.128 s
%------------------------------------------------------------------------------
