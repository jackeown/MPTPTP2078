%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 111 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :  160 ( 270 expanded)
%              Number of equality atoms :   43 (  84 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f56,f64,f74,f82,f98,f103,f125,f131,f188])).

fof(f188,plain,
    ( ~ spl3_10
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl3_10
    | spl3_15 ),
    inference(subsumption_resolution,[],[f186,f97])).

fof(f97,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_10
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f186,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl3_15 ),
    inference(forward_demodulation,[],[f181,f30])).

fof(f30,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f181,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_15 ),
    inference(resolution,[],[f28,f130])).

fof(f130,plain,
    ( ~ m1_subset_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_15
  <=> m1_subset_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f131,plain,
    ( ~ spl3_15
    | spl3_14 ),
    inference(avatar_split_clause,[],[f126,f122,f128])).

fof(f122,plain,
    ( spl3_14
  <=> r1_tarski(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f126,plain,
    ( ~ m1_subset_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0))
    | spl3_14 ),
    inference(unit_resulting_resolution,[],[f124,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f124,plain,
    ( ~ r1_tarski(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_xboole_0)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f125,plain,
    ( ~ spl3_14
    | spl3_11 ),
    inference(avatar_split_clause,[],[f118,f100,f122])).

fof(f100,plain,
    ( spl3_11
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f118,plain,
    ( ~ r1_tarski(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_xboole_0)
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f102,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f22,f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f102,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f103,plain,
    ( ~ spl3_11
    | spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f86,f78,f32,f100])).

fof(f32,plain,
    ( spl3_1
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f78,plain,
    ( spl3_8
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f86,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl3_1
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f34,f80])).

fof(f80,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f34,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f98,plain,
    ( spl3_10
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f85,f78,f53,f95])).

fof(f53,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f85,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f55,f80])).

fof(f55,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f82,plain,
    ( spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f76,f71,f78])).

fof(f71,plain,
    ( spl3_7
  <=> k1_xboole_0 = k2_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f76,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_7 ),
    inference(superposition,[],[f21,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f74,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f67,f60,f71])).

fof(f60,plain,
    ( spl3_6
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f67,plain,
    ( k1_xboole_0 = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f62,f22])).

fof(f62,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f64,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f58,f53,f60])).

fof(f58,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_5 ),
    inference(resolution,[],[f23,f55])).

fof(f56,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f51,f37,f53])).

fof(f37,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f51,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f39,f30])).

fof(f39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_2(sK2,k1_xboole_0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_2(sK2,k1_xboole_0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(f35,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f32])).

fof(f20,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (22714)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (22714)Refutation not found, incomplete strategy% (22714)------------------------------
% 0.21/0.47  % (22714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (22714)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (22714)Memory used [KB]: 6140
% 0.21/0.47  % (22714)Time elapsed: 0.061 s
% 0.21/0.47  % (22714)------------------------------
% 0.21/0.47  % (22714)------------------------------
% 0.21/0.48  % (22730)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (22728)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (22730)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f35,f40,f56,f64,f74,f82,f98,f103,f125,f131,f188])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ~spl3_10 | spl3_15),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f187])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    $false | (~spl3_10 | spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f186,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl3_10 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl3_15),
% 0.21/0.48    inference(forward_demodulation,[],[f181,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_15),
% 0.21/0.48    inference(resolution,[],[f28,f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ~m1_subset_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0)) | spl3_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    spl3_15 <=> m1_subset_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ~spl3_15 | spl3_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f126,f122,f128])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    spl3_14 <=> r1_tarski(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ~m1_subset_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0)) | spl3_14),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f124,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ~r1_tarski(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_xboole_0) | spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f122])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ~spl3_14 | spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f118,f100,f122])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl3_11 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ~r1_tarski(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_xboole_0) | spl3_11),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f102,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(superposition,[],[f22,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ~spl3_11 | spl3_1 | ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f86,f78,f32,f100])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    spl3_1 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl3_8 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (spl3_1 | ~spl3_8)),
% 0.21/0.48    inference(backward_demodulation,[],[f34,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f78])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f32])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl3_10 | ~spl3_5 | ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f85,f78,f53,f95])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_5 | ~spl3_8)),
% 0.21/0.48    inference(backward_demodulation,[],[f55,f80])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f53])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl3_8 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f76,f71,f78])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl3_7 <=> k1_xboole_0 = k2_xboole_0(sK2,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl3_7),
% 0.21/0.48    inference(superposition,[],[f21,f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    k1_xboole_0 = k2_xboole_0(sK2,k1_xboole_0) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f71])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl3_7 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f67,f60,f71])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl3_6 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    k1_xboole_0 = k2_xboole_0(sK2,k1_xboole_0) | ~spl3_6),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f62,f22])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    r1_tarski(sK2,k1_xboole_0) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl3_6 | ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f58,f53,f60])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    r1_tarski(sK2,k1_xboole_0) | ~spl3_5),
% 0.21/0.48    inference(resolution,[],[f23,f55])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl3_5 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f51,f37,f53])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_2),
% 0.21/0.48    inference(forward_demodulation,[],[f39,f30])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f37])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f37])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f32])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (22730)------------------------------
% 0.21/0.48  % (22730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22730)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (22730)Memory used [KB]: 10746
% 0.21/0.48  % (22730)Time elapsed: 0.075 s
% 0.21/0.48  % (22730)------------------------------
% 0.21/0.48  % (22730)------------------------------
% 0.21/0.48  % (22713)Success in time 0.124 s
%------------------------------------------------------------------------------
