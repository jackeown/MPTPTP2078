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
% DateTime   : Thu Dec  3 12:54:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 106 expanded)
%              Number of leaves         :   19 (  49 expanded)
%              Depth                    :    6
%              Number of atoms          :  180 ( 270 expanded)
%              Number of equality atoms :   41 (  65 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f47,f51,f59,f63,f71,f78,f84,f90,f96,f101,f105])).

fof(f105,plain,
    ( spl2_1
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl2_1
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f103,f29])).

fof(f29,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f103,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f102,f50])).

fof(f50,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_6
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f102,plain,
    ( k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(superposition,[],[f100,f89])).

fof(f89,plain,
    ( k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_14
  <=> k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f100,plain,
    ( ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_16
  <=> ! [X1,X0] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f101,plain,
    ( spl2_16
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f97,f94,f45,f99])).

fof(f45,plain,
    ( spl2_5
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f94,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f97,plain,
    ( ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(resolution,[],[f95,f46])).

fof(f46,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,
    ( spl2_15
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f92,f57,f49,f45,f94])).

fof(f57,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f91,f50])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,k2_relat_1(k6_relat_1(X1))) )
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(resolution,[],[f58,f46])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f90,plain,
    ( spl2_14
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f85,f82,f75,f87])).

fof(f75,plain,
    ( spl2_12
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f82,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f85,plain,
    ( k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(resolution,[],[f83,f77])).

fof(f77,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f75])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,
    ( spl2_13
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f80,f61,f49,f45,f82])).

fof(f61,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f79,f50])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(resolution,[],[f62,f46])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1 )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f78,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f72,f69,f32,f75])).

fof(f32,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f69,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f72,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(resolution,[],[f70,f34])).

fof(f34,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f24,f69])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f63,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f23,f61])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f59,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f22,f57])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f51,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f47,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f17,f45])).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f30,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f16,f27])).

fof(f16,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:58:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.41  % (1529)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.42  % (1528)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (1527)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (1526)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (1526)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f30,f35,f47,f51,f59,f63,f71,f78,f84,f90,f96,f101,f105])).
% 0.21/0.43  fof(f105,plain,(
% 0.21/0.43    spl2_1 | ~spl2_6 | ~spl2_14 | ~spl2_16),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f104])).
% 0.21/0.43  fof(f104,plain,(
% 0.21/0.43    $false | (spl2_1 | ~spl2_6 | ~spl2_14 | ~spl2_16)),
% 0.21/0.43    inference(subsumption_resolution,[],[f103,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    spl2_1 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f103,plain,(
% 0.21/0.43    sK1 = k9_relat_1(k6_relat_1(sK0),sK1) | (~spl2_6 | ~spl2_14 | ~spl2_16)),
% 0.21/0.43    inference(forward_demodulation,[],[f102,f50])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl2_6 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1)) | (~spl2_14 | ~spl2_16)),
% 0.21/0.43    inference(superposition,[],[f100,f89])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) | ~spl2_14),
% 0.21/0.43    inference(avatar_component_clause,[],[f87])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    spl2_14 <=> k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)) ) | ~spl2_16),
% 0.21/0.43    inference(avatar_component_clause,[],[f99])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    spl2_16 <=> ! [X1,X0] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.43  fof(f101,plain,(
% 0.21/0.43    spl2_16 | ~spl2_5 | ~spl2_15),
% 0.21/0.43    inference(avatar_split_clause,[],[f97,f94,f45,f99])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl2_5 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    spl2_15 <=> ! [X1,X0] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1) | ~v1_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_5 | ~spl2_15)),
% 0.21/0.43    inference(resolution,[],[f95,f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f45])).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1)) ) | ~spl2_15),
% 0.21/0.43    inference(avatar_component_clause,[],[f94])).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    spl2_15 | ~spl2_5 | ~spl2_6 | ~spl2_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f92,f57,f49,f45,f94])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl2_8 <=> ! [X1,X0] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1) | ~v1_relat_1(X0)) ) | (~spl2_5 | ~spl2_6 | ~spl2_8)),
% 0.21/0.43    inference(forward_demodulation,[],[f91,f50])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,k2_relat_1(k6_relat_1(X1)))) ) | (~spl2_5 | ~spl2_8)),
% 0.21/0.43    inference(resolution,[],[f58,f46])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) ) | ~spl2_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f57])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    spl2_14 | ~spl2_12 | ~spl2_13),
% 0.21/0.43    inference(avatar_split_clause,[],[f85,f82,f75,f87])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    spl2_12 <=> r1_tarski(sK1,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    spl2_13 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) | (~spl2_12 | ~spl2_13)),
% 0.21/0.43    inference(resolution,[],[f83,f77])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    r1_tarski(sK1,sK0) | ~spl2_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f75])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | ~spl2_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f82])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    spl2_13 | ~spl2_5 | ~spl2_6 | ~spl2_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f80,f61,f49,f45,f82])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    spl2_9 <=> ! [X1,X0] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | (~spl2_5 | ~spl2_6 | ~spl2_9)),
% 0.21/0.43    inference(forward_demodulation,[],[f79,f50])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | (~spl2_5 | ~spl2_9)),
% 0.21/0.43    inference(resolution,[],[f62,f46])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) ) | ~spl2_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f61])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    spl2_12 | ~spl2_2 | ~spl2_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f72,f69,f32,f75])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    spl2_11 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    r1_tarski(sK1,sK0) | (~spl2_2 | ~spl2_11)),
% 0.21/0.43    inference(resolution,[],[f70,f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f32])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f69])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl2_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f69])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.43    inference(nnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl2_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f61])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    spl2_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f57])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    spl2_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f49])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl2_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f45])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f15,f32])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.44    inference(negated_conjecture,[],[f6])).
% 0.21/0.44  fof(f6,conjecture,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ~spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f16,f27])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (1526)------------------------------
% 0.21/0.44  % (1526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (1526)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (1526)Memory used [KB]: 10618
% 0.21/0.44  % (1526)Time elapsed: 0.006 s
% 0.21/0.44  % (1526)------------------------------
% 0.21/0.44  % (1526)------------------------------
% 0.21/0.44  % (1520)Success in time 0.078 s
%------------------------------------------------------------------------------
