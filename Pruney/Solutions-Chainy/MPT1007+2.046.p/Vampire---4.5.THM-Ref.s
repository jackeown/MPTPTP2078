%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:58 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 126 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  165 ( 345 expanded)
%              Number of equality atoms :   50 ( 104 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f111,f126,f128,f133,f143])).

fof(f143,plain,(
    ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f63,f20,f65,f24,f137,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f137,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl4_9 ),
    inference(superposition,[],[f61,f124])).

fof(f124,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_9
  <=> k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f61,plain,(
    ! [X3,X1] : r2_hidden(X3,k1_enumset1(X3,X3,X1)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f26])).

% (4019)Refutation not found, incomplete strategy% (4019)------------------------------
% (4019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4019)Termination reason: Refutation not found, incomplete strategy

% (4019)Memory used [KB]: 10618
% (4019)Time elapsed: 0.120 s
% (4019)------------------------------
% (4019)------------------------------
fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f24,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f65,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f31,f45])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f22,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

% (4015)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f133,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f23,f108])).

fof(f108,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f128,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f45,f120])).

fof(f120,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f126,plain,
    ( ~ spl4_8
    | spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f115,f102,f122,f118])).

fof(f102,plain,
    ( spl4_6
  <=> k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f115,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f29,f104])).

fof(f104,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f111,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f46,f100])).

fof(f100,plain,
    ( ~ v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_5
  <=> v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f46,plain,(
    v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f21,f44])).

fof(f21,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f109,plain,
    ( ~ spl4_5
    | spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f96,f106,f102,f98])).

fof(f96,plain,
    ( k1_xboole_0 = sK1
    | k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f37,f45])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n021.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:28:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.25/0.53  % (4007)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.25/0.53  % (4019)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.36/0.53  % (4028)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.36/0.53  % (4013)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.53  % (4020)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.36/0.54  % (4012)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.36/0.54  % (4020)Refutation found. Thanks to Tanya!
% 1.36/0.54  % SZS status Theorem for theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f145,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(avatar_sat_refutation,[],[f109,f111,f126,f128,f133,f143])).
% 1.36/0.54  fof(f143,plain,(
% 1.36/0.54    ~spl4_9),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f142])).
% 1.36/0.54  fof(f142,plain,(
% 1.36/0.54    $false | ~spl4_9),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f63,f20,f65,f24,f137,f27])).
% 1.36/0.54  fof(f27,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,plain,(
% 1.36/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.36/0.54    inference(flattening,[],[f13])).
% 1.36/0.54  fof(f13,plain,(
% 1.36/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.36/0.54    inference(ennf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 1.36/0.54  fof(f137,plain,(
% 1.36/0.54    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl4_9),
% 1.36/0.54    inference(superposition,[],[f61,f124])).
% 1.36/0.54  fof(f124,plain,(
% 1.36/0.54    k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2) | ~spl4_9),
% 1.36/0.54    inference(avatar_component_clause,[],[f122])).
% 1.36/0.54  fof(f122,plain,(
% 1.36/0.54    spl4_9 <=> k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.36/0.54  fof(f61,plain,(
% 1.36/0.54    ( ! [X3,X1] : (r2_hidden(X3,k1_enumset1(X3,X3,X1))) )),
% 1.36/0.54    inference(equality_resolution,[],[f60])).
% 1.36/0.54  fof(f60,plain,(
% 1.36/0.54    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k1_enumset1(X3,X3,X1) != X2) )),
% 1.36/0.54    inference(equality_resolution,[],[f48])).
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.36/0.54    inference(definition_unfolding,[],[f42,f26])).
% 1.36/0.54  % (4019)Refutation not found, incomplete strategy% (4019)------------------------------
% 1.36/0.54  % (4019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (4019)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (4019)Memory used [KB]: 10618
% 1.36/0.54  % (4019)Time elapsed: 0.120 s
% 1.36/0.54  % (4019)------------------------------
% 1.36/0.54  % (4019)------------------------------
% 1.36/0.54  fof(f26,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.54  fof(f42,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.36/0.54    inference(cnf_transformation,[],[f1])).
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.36/0.54  fof(f24,plain,(
% 1.36/0.54    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 1.36/0.54    inference(cnf_transformation,[],[f12])).
% 1.36/0.54  fof(f12,plain,(
% 1.36/0.54    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.36/0.54    inference(flattening,[],[f11])).
% 1.36/0.54  fof(f11,plain,(
% 1.36/0.54    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.36/0.54    inference(ennf_transformation,[],[f10])).
% 1.36/0.54  fof(f10,negated_conjecture,(
% 1.36/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.36/0.54    inference(negated_conjecture,[],[f9])).
% 1.36/0.54  fof(f9,conjecture,(
% 1.36/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 1.36/0.54  fof(f65,plain,(
% 1.36/0.54    v5_relat_1(sK2,sK1)),
% 1.36/0.54    inference(resolution,[],[f31,f45])).
% 1.36/0.54  fof(f45,plain,(
% 1.36/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 1.36/0.54    inference(definition_unfolding,[],[f22,f44])).
% 1.36/0.54  fof(f44,plain,(
% 1.36/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f25,f26])).
% 1.36/0.54  fof(f25,plain,(
% 1.36/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f2])).
% 1.36/0.54  fof(f2,axiom,(
% 1.36/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.36/0.54  fof(f22,plain,(
% 1.36/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.36/0.54    inference(cnf_transformation,[],[f12])).
% 1.36/0.54  fof(f31,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f17])).
% 1.36/0.54  % (4015)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.36/0.54  fof(f17,plain,(
% 1.36/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.54    inference(ennf_transformation,[],[f6])).
% 1.36/0.54  fof(f6,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.36/0.54  fof(f20,plain,(
% 1.36/0.54    v1_funct_1(sK2)),
% 1.36/0.54    inference(cnf_transformation,[],[f12])).
% 1.36/0.54  fof(f63,plain,(
% 1.36/0.54    v1_relat_1(sK2)),
% 1.36/0.54    inference(resolution,[],[f45,f28])).
% 1.36/0.54  fof(f28,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f15])).
% 1.36/0.54  fof(f15,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.54    inference(ennf_transformation,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.36/0.54  fof(f133,plain,(
% 1.36/0.54    ~spl4_7),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f129])).
% 1.36/0.54  fof(f129,plain,(
% 1.36/0.54    $false | ~spl4_7),
% 1.36/0.54    inference(subsumption_resolution,[],[f23,f108])).
% 1.36/0.54  fof(f108,plain,(
% 1.36/0.54    k1_xboole_0 = sK1 | ~spl4_7),
% 1.36/0.54    inference(avatar_component_clause,[],[f106])).
% 1.36/0.54  fof(f106,plain,(
% 1.36/0.54    spl4_7 <=> k1_xboole_0 = sK1),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.36/0.54  fof(f23,plain,(
% 1.36/0.54    k1_xboole_0 != sK1),
% 1.36/0.54    inference(cnf_transformation,[],[f12])).
% 1.36/0.54  fof(f128,plain,(
% 1.36/0.54    spl4_8),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f127])).
% 1.36/0.54  fof(f127,plain,(
% 1.36/0.54    $false | spl4_8),
% 1.36/0.54    inference(subsumption_resolution,[],[f45,f120])).
% 1.36/0.54  fof(f120,plain,(
% 1.36/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) | spl4_8),
% 1.36/0.54    inference(avatar_component_clause,[],[f118])).
% 1.36/0.54  fof(f118,plain,(
% 1.36/0.54    spl4_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.36/0.54  fof(f126,plain,(
% 1.36/0.54    ~spl4_8 | spl4_9 | ~spl4_6),
% 1.36/0.54    inference(avatar_split_clause,[],[f115,f102,f122,f118])).
% 1.36/0.54  fof(f102,plain,(
% 1.36/0.54    spl4_6 <=> k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.36/0.54  fof(f115,plain,(
% 1.36/0.54    k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) | ~spl4_6),
% 1.36/0.54    inference(superposition,[],[f29,f104])).
% 1.36/0.54  fof(f104,plain,(
% 1.36/0.54    k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) | ~spl4_6),
% 1.36/0.54    inference(avatar_component_clause,[],[f102])).
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f16])).
% 1.36/0.54  fof(f16,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.54    inference(ennf_transformation,[],[f7])).
% 1.36/0.54  fof(f7,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.36/0.54  fof(f111,plain,(
% 1.36/0.54    spl4_5),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f110])).
% 1.36/0.54  fof(f110,plain,(
% 1.36/0.54    $false | spl4_5),
% 1.36/0.54    inference(subsumption_resolution,[],[f46,f100])).
% 1.36/0.54  fof(f100,plain,(
% 1.36/0.54    ~v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) | spl4_5),
% 1.36/0.54    inference(avatar_component_clause,[],[f98])).
% 1.36/0.54  fof(f98,plain,(
% 1.36/0.54    spl4_5 <=> v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.36/0.54  fof(f46,plain,(
% 1.36/0.54    v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)),
% 1.36/0.54    inference(definition_unfolding,[],[f21,f44])).
% 1.36/0.54  fof(f21,plain,(
% 1.36/0.54    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.36/0.54    inference(cnf_transformation,[],[f12])).
% 1.36/0.54  fof(f109,plain,(
% 1.36/0.54    ~spl4_5 | spl4_6 | spl4_7),
% 1.36/0.54    inference(avatar_split_clause,[],[f96,f106,f102,f98])).
% 1.36/0.54  fof(f96,plain,(
% 1.36/0.54    k1_xboole_0 = sK1 | k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) | ~v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)),
% 1.36/0.54    inference(resolution,[],[f37,f45])).
% 1.36/0.54  fof(f37,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f19])).
% 1.36/0.54  fof(f19,plain,(
% 1.36/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.54    inference(flattening,[],[f18])).
% 1.36/0.54  fof(f18,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.54    inference(ennf_transformation,[],[f8])).
% 1.36/0.54  fof(f8,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (4020)------------------------------
% 1.36/0.54  % (4020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (4020)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (4020)Memory used [KB]: 6268
% 1.36/0.54  % (4020)Time elapsed: 0.109 s
% 1.36/0.54  % (4020)------------------------------
% 1.36/0.54  % (4020)------------------------------
% 1.36/0.54  % (4006)Success in time 0.18 s
%------------------------------------------------------------------------------
