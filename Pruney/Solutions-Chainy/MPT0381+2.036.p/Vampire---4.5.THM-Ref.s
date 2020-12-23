%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 106 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  198 ( 303 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39,f43,f55,f64,f72,f81,f91,f95,f109,f171,f199,f201])).

fof(f201,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_17
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_17
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f198,f195])).

fof(f195,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_17
    | ~ spl3_25 ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl3_1
    | spl3_2
    | ~ spl3_17
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f108,f179])).

fof(f179,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1
    | spl3_2
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f176,f34])).

fof(f34,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f176,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK0,sK1)
    | spl3_2
    | ~ spl3_25 ),
    inference(resolution,[],[f170,f38])).

% (21077)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f38,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_2
  <=> m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ r2_hidden(X1,X0) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl3_25
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f108,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_17
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f198,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl3_27
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f199,plain,
    ( spl3_27
    | ~ spl3_1
    | spl3_2
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f180,f169,f37,f33,f197])).

fof(f180,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f34,f179])).

fof(f171,plain,
    ( spl3_25
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f104,f89,f70,f169])).

fof(f70,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f89,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,X0)
        | k1_xboole_0 = X0
        | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(resolution,[],[f90,f71])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k1_xboole_0 = X0
        | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f109,plain,
    ( spl3_17
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f102,f93,f62,f107])).

fof(f62,plain,
    ( spl3_8
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f93,plain,
    ( spl3_15
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f102,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(superposition,[],[f63,f94])).

fof(f94,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f93])).

fof(f63,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
        | ~ r2_hidden(X3,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f95,plain,
    ( spl3_15
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f87,f79,f33,f93])).

fof(f79,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f87,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(resolution,[],[f80,f34])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f79])).

fof(f91,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f19,f89])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k1_xboole_0 = X0
      | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f81,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f20,f79])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f72,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f56,f53,f41,f70])).

fof(f41,plain,
    ( spl3_3
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f53,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f54,f42])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f64,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f55,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f17,f53])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f43,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f41])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f39,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f14,f37])).

fof(f14,plain,(
    ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f35,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f13,f33])).

fof(f13,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:38:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.43  % (21071)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.45  % (21075)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (21069)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.46  % (21068)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.46  % (21075)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (21079)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f202,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f35,f39,f43,f55,f64,f72,f81,f91,f95,f109,f171,f199,f201])).
% 0.20/0.47  fof(f201,plain,(
% 0.20/0.47    ~spl3_1 | spl3_2 | ~spl3_17 | ~spl3_25 | ~spl3_27),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f200])).
% 0.20/0.47  fof(f200,plain,(
% 0.20/0.47    $false | (~spl3_1 | spl3_2 | ~spl3_17 | ~spl3_25 | ~spl3_27)),
% 0.20/0.47    inference(subsumption_resolution,[],[f198,f195])).
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | (~spl3_1 | spl3_2 | ~spl3_17 | ~spl3_25)),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f184])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0)) ) | (~spl3_1 | spl3_2 | ~spl3_17 | ~spl3_25)),
% 0.20/0.47    inference(backward_demodulation,[],[f108,f179])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | (~spl3_1 | spl3_2 | ~spl3_25)),
% 0.20/0.47    inference(subsumption_resolution,[],[f176,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    r2_hidden(sK0,sK1) | ~spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    spl3_1 <=> r2_hidden(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | ~r2_hidden(sK0,sK1) | (spl3_2 | ~spl3_25)),
% 0.20/0.47    inference(resolution,[],[f170,f38])).
% 0.20/0.47  % (21077)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) | spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    spl3_2 <=> m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~r2_hidden(X1,X0)) ) | ~spl3_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f169])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    spl3_25 <=> ! [X1,X0] : (k1_xboole_0 = X0 | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | ~r2_hidden(X1,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,sK1)) ) | ~spl3_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f107])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    spl3_17 <=> ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.47  fof(f198,plain,(
% 0.20/0.47    r2_hidden(sK0,k1_xboole_0) | ~spl3_27),
% 0.20/0.47    inference(avatar_component_clause,[],[f197])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    spl3_27 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.47  fof(f199,plain,(
% 0.20/0.47    spl3_27 | ~spl3_1 | spl3_2 | ~spl3_25),
% 0.20/0.47    inference(avatar_split_clause,[],[f180,f169,f37,f33,f197])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    r2_hidden(sK0,k1_xboole_0) | (~spl3_1 | spl3_2 | ~spl3_25)),
% 0.20/0.47    inference(backward_demodulation,[],[f34,f179])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    spl3_25 | ~spl3_10 | ~spl3_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f104,f89,f70,f169])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl3_10 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl3_14 <=> ! [X1,X0] : (~m1_subset_1(X1,X0) | k1_xboole_0 = X0 | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = X0 | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | ~r2_hidden(X1,X0)) ) | (~spl3_10 | ~spl3_14)),
% 0.20/0.47    inference(resolution,[],[f90,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) ) | ~spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f70])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k1_xboole_0 = X0 | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))) ) | ~spl3_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f89])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    spl3_17 | ~spl3_8 | ~spl3_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f102,f93,f62,f107])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl3_8 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl3_15 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,sK1)) ) | (~spl3_8 | ~spl3_15)),
% 0.20/0.47    inference(superposition,[],[f63,f94])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | ~spl3_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f93])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) ) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f62])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    spl3_15 | ~spl3_1 | ~spl3_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f87,f79,f33,f93])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl3_12 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | (~spl3_1 | ~spl3_12)),
% 0.20/0.47    inference(resolution,[],[f80,f34])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0) ) | ~spl3_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f79])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl3_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f89])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k1_xboole_0 = X0 | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    spl3_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f79])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    spl3_10 | ~spl3_3 | ~spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f56,f53,f41,f70])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    spl3_3 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl3_6 <=> ! [X1,X0] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) ) | (~spl3_3 | ~spl3_6)),
% 0.20/0.47    inference(subsumption_resolution,[],[f54,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) ) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f41])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) ) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f53])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f62])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(equality_resolution,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f17,f53])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f41])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f14,f37])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.47    inference(negated_conjecture,[],[f6])).
% 0.20/0.47  fof(f6,conjecture,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f13,f33])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (21075)------------------------------
% 0.20/0.47  % (21075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (21075)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (21075)Memory used [KB]: 10618
% 0.20/0.47  % (21075)Time elapsed: 0.057 s
% 0.20/0.47  % (21075)------------------------------
% 0.20/0.47  % (21075)------------------------------
% 0.20/0.47  % (21065)Success in time 0.119 s
%------------------------------------------------------------------------------
