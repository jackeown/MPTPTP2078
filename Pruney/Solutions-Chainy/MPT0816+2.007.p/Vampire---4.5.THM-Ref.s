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
% DateTime   : Thu Dec  3 12:56:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  82 expanded)
%              Number of leaves         :   14 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  128 ( 204 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f44,f50,f56,f71,f94,f118])).

fof(f118,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_13 ),
    inference(subsumption_resolution,[],[f116,f38])).

fof(f38,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_3
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f116,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_2
    | spl3_13 ),
    inference(subsumption_resolution,[],[f113,f33])).

fof(f33,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_2
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f113,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_13 ),
    inference(resolution,[],[f93,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f93,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_13
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f94,plain,
    ( ~ spl3_13
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f89,f69,f41,f91])).

fof(f41,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f69,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f89,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f80,f43])).

fof(f43,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f80,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(resolution,[],[f70,f19])).

fof(f19,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f70,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f59,f54,f69])).

fof(f54,plain,
    ( spl3_6
  <=> ! [X0] : ~ r1_tarski(k2_xboole_0(sK2,X0),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(sK2,X0) )
    | ~ spl3_6 ),
    inference(superposition,[],[f55,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f55,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK2,X0),k2_zfmisc_1(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f56,plain,
    ( spl3_6
    | spl3_5 ),
    inference(avatar_split_clause,[],[f52,f47,f54])).

fof(f47,plain,
    ( spl3_5
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f52,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK2,X0),k2_zfmisc_1(sK0,sK1))
    | spl3_5 ),
    inference(resolution,[],[f23,f49])).

fof(f49,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f50,plain,
    ( ~ spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f45,f26,f47])).

fof(f26,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f45,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | spl3_1 ),
    inference(resolution,[],[f21,f28])).

fof(f28,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f44,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f41])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & r1_tarski(k2_relat_1(X2),X1)
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & r1_tarski(k2_relat_1(X2),X1)
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r1_tarski(k2_relat_1(X2),X1)
            & r1_tarski(k1_relat_1(X2),X0) )
         => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f39,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f31])).

fof(f17,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f26])).

fof(f18,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (9156)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (9154)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.43  % (9157)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.44  % (9155)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.44  % (9150)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.44  % (9159)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.44  % (9150)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f128,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f29,f34,f39,f44,f50,f56,f71,f94,f118])).
% 0.20/0.44  fof(f118,plain,(
% 0.20/0.44    ~spl3_2 | ~spl3_3 | spl3_13),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f117])).
% 0.20/0.44  fof(f117,plain,(
% 0.20/0.44    $false | (~spl3_2 | ~spl3_3 | spl3_13)),
% 0.20/0.44    inference(subsumption_resolution,[],[f116,f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    spl3_3 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.44  fof(f116,plain,(
% 0.20/0.44    ~r1_tarski(k1_relat_1(sK2),sK0) | (~spl3_2 | spl3_13)),
% 0.20/0.44    inference(subsumption_resolution,[],[f113,f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    spl3_2 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.44  fof(f113,plain,(
% 0.20/0.44    ~r1_tarski(k2_relat_1(sK2),sK1) | ~r1_tarski(k1_relat_1(sK2),sK0) | spl3_13),
% 0.20/0.44    inference(resolution,[],[f93,f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(flattening,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).
% 0.20/0.44  fof(f93,plain,(
% 0.20/0.44    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1)) | spl3_13),
% 0.20/0.44    inference(avatar_component_clause,[],[f91])).
% 0.20/0.44  fof(f91,plain,(
% 0.20/0.44    spl3_13 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.44  fof(f94,plain,(
% 0.20/0.44    ~spl3_13 | ~spl3_4 | ~spl3_9),
% 0.20/0.44    inference(avatar_split_clause,[],[f89,f69,f41,f91])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    spl3_4 <=> v1_relat_1(sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    spl3_9 <=> ! [X0] : (~r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(sK2,X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.44  fof(f89,plain,(
% 0.20/0.44    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1)) | (~spl3_4 | ~spl3_9)),
% 0.20/0.44    inference(subsumption_resolution,[],[f80,f43])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    v1_relat_1(sK2) | ~spl3_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f41])).
% 0.20/0.44  fof(f80,plain,(
% 0.20/0.44    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1)) | ~v1_relat_1(sK2) | ~spl3_9),
% 0.20/0.44    inference(resolution,[],[f70,f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.20/0.44  fof(f70,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_tarski(sK2,X0) | ~r1_tarski(X0,k2_zfmisc_1(sK0,sK1))) ) | ~spl3_9),
% 0.20/0.44    inference(avatar_component_clause,[],[f69])).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    spl3_9 | ~spl3_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f59,f54,f69])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    spl3_6 <=> ! [X0] : ~r1_tarski(k2_xboole_0(sK2,X0),k2_zfmisc_1(sK0,sK1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(sK2,X0)) ) | ~spl3_6),
% 0.20/0.44    inference(superposition,[],[f55,f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK2,X0),k2_zfmisc_1(sK0,sK1))) ) | ~spl3_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f54])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    spl3_6 | spl3_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f52,f47,f54])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    spl3_5 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK2,X0),k2_zfmisc_1(sK0,sK1))) ) | spl3_5),
% 0.20/0.44    inference(resolution,[],[f23,f49])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    ~r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | spl3_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f47])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    ~spl3_5 | spl3_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f45,f26,f47])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    ~r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | spl3_1),
% 0.20/0.44    inference(resolution,[],[f21,f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f26])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    spl3_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f15,f41])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    v1_relat_1(sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2))),
% 0.20/0.44    inference(flattening,[],[f8])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & (r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0))) & v1_relat_1(X2))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.44    inference(negated_conjecture,[],[f6])).
% 0.20/0.44  fof(f6,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    spl3_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f16,f36])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    spl3_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f17,f31])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ~spl3_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f18,f26])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (9150)------------------------------
% 0.20/0.44  % (9150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (9150)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (9150)Memory used [KB]: 10618
% 0.20/0.44  % (9150)Time elapsed: 0.028 s
% 0.20/0.44  % (9150)------------------------------
% 0.20/0.44  % (9150)------------------------------
% 0.20/0.45  % (9148)Success in time 0.09 s
%------------------------------------------------------------------------------
