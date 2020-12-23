%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 127 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  158 ( 336 expanded)
%              Number of equality atoms :   25 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f118,f126,f129,f136,f147,f154])).

fof(f154,plain,
    ( spl3_1
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl3_1
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f95,f146])).

fof(f146,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl3_8
  <=> r1_tarski(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f95,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | spl3_1 ),
    inference(backward_demodulation,[],[f71,f49])).

fof(f49,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f21,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
            & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
          & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).

fof(f71,plain,
    ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_1
  <=> r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f147,plain,
    ( ~ spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f142,f144,f123])).

fof(f123,plain,
    ( spl3_7
  <=> v1_relat_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f142,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(global_subsumption,[],[f50,f46])).

fof(f46,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f44,f26])).

fof(f26,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f44,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2)) ),
    inference(resolution,[],[f22,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f22,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f21,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f136,plain,
    ( spl3_2
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f93,f113])).

fof(f113,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_5
  <=> sK1 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f93,plain,
    ( sK1 != k1_relat_1(sK2)
    | spl3_2 ),
    inference(superposition,[],[f75,f48])).

fof(f48,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f21,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f75,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_2
  <=> sK1 = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f129,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f125,f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f125,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f126,plain,
    ( spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f120,f123,f115])).

fof(f115,plain,
    ( spl3_6
  <=> r1_tarski(sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f120,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(global_subsumption,[],[f50,f45])).

fof(f45,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f43,f25])).

fof(f25,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f43,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2)) ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f118,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f78,f115,f111])).

fof(f78,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | sK1 = k1_relat_1(sK2) ),
    inference(resolution,[],[f67,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f67,plain,(
    r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(resolution,[],[f66,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f66,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(global_subsumption,[],[f21,f65])).

fof(f65,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f47,f36])).

fof(f47,plain,(
    m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f21,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f76,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f20,f73,f69])).

fof(f20,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:55:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (30122)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.46  % (30134)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.48  % (30134)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f76,f118,f126,f129,f136,f147,f154])).
% 0.20/0.48  fof(f154,plain,(
% 0.20/0.48    spl3_1 | ~spl3_8),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f148])).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    $false | (spl3_1 | ~spl3_8)),
% 0.20/0.48    inference(subsumption_resolution,[],[f95,f146])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    r1_tarski(sK1,k2_relat_1(sK2)) | ~spl3_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f144])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    spl3_8 <=> r1_tarski(sK1,k2_relat_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ~r1_tarski(sK1,k2_relat_1(sK2)) | spl3_1),
% 0.20/0.48    inference(backward_demodulation,[],[f71,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.20/0.48    inference(resolution,[],[f21,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f10])).
% 0.20/0.48  fof(f10,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f69])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    spl3_1 <=> r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    ~spl3_7 | spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f142,f144,f123])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    spl3_7 <=> v1_relat_1(k6_relat_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    r1_tarski(sK1,k2_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.20/0.48    inference(global_subsumption,[],[f50,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    r1_tarski(sK1,k2_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2)),
% 0.20/0.48    inference(forward_demodulation,[],[f44,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ~v1_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2) | r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f22,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(resolution,[],[f21,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    spl3_2 | ~spl3_5),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f130])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    $false | (spl3_2 | ~spl3_5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f93,f113])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    sK1 = k1_relat_1(sK2) | ~spl3_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f111])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    spl3_5 <=> sK1 = k1_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    sK1 != k1_relat_1(sK2) | spl3_2),
% 0.20/0.48    inference(superposition,[],[f75,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.20/0.48    inference(resolution,[],[f21,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    sK1 != k1_relset_1(sK1,sK0,sK2) | spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f73])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    spl3_2 <=> sK1 = k1_relset_1(sK1,sK0,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    spl3_7),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f127])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    $false | spl3_7),
% 0.20/0.48    inference(resolution,[],[f125,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    ~v1_relat_1(k6_relat_1(sK1)) | spl3_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f123])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    spl3_6 | ~spl3_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f120,f123,f115])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    spl3_6 <=> r1_tarski(sK1,k1_relat_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ~v1_relat_1(k6_relat_1(sK1)) | r1_tarski(sK1,k1_relat_1(sK2))),
% 0.20/0.48    inference(global_subsumption,[],[f50,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    r1_tarski(sK1,k1_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2)),
% 0.20/0.48    inference(forward_demodulation,[],[f43,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ~v1_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2) | r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f22,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    spl3_5 | ~spl3_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f78,f115,f111])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ~r1_tarski(sK1,k1_relat_1(sK2)) | sK1 = k1_relat_1(sK2)),
% 0.20/0.48    inference(resolution,[],[f67,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    r1_tarski(k1_relat_1(sK2),sK1)),
% 0.20/0.48    inference(resolution,[],[f66,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.20/0.48    inference(global_subsumption,[],[f21,f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.48    inference(superposition,[],[f47,f36])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))),
% 0.20/0.48    inference(resolution,[],[f21,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    ~spl3_1 | ~spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f20,f73,f69])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    sK1 != k1_relset_1(sK1,sK0,sK2) | ~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (30134)------------------------------
% 0.20/0.48  % (30134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30134)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (30134)Memory used [KB]: 10618
% 0.20/0.48  % (30134)Time elapsed: 0.081 s
% 0.20/0.48  % (30134)------------------------------
% 0.20/0.48  % (30134)------------------------------
% 0.20/0.48  % (30112)Success in time 0.13 s
%------------------------------------------------------------------------------
