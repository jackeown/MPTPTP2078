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
% DateTime   : Thu Dec  3 12:59:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  96 expanded)
%              Number of leaves         :   11 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :  131 ( 237 expanded)
%              Number of equality atoms :   95 ( 182 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f78,f82,f90,f114])).

fof(f114,plain,
    ( ~ spl2_4
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl2_4
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f89,f89,f89,f89,f76,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f18,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f17,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f76,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl2_4
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f89,plain,
    ( k1_xboole_0 != sK0
    | spl2_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f90,plain,
    ( ~ spl2_5
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f84,f71,f41,f87])).

fof(f41,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f71,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f84,plain,
    ( k1_xboole_0 != sK0
    | spl2_1
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f43,f73])).

fof(f73,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f43,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f82,plain,
    ( spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f43,f48,f77,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f25,f16,f16,f16])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f77,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f48,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_2
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f78,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f68,f46,f75,f71])).

fof(f68,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(superposition,[],[f32,f48])).

fof(f49,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f46])).

fof(f27,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    inference(definition_unfolding,[],[f14,f26,f26])).

% (10995)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f14,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK0 != sK1
    & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).

% (10998)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f10,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) )
   => ( sK0 != sK1
      & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f44,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f15,f41])).

fof(f15,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (10993)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (10971)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (10971)Refutation not found, incomplete strategy% (10971)------------------------------
% 0.21/0.51  % (10971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10973)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (10971)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10971)Memory used [KB]: 1663
% 0.21/0.51  % (10971)Time elapsed: 0.107 s
% 0.21/0.51  % (10971)------------------------------
% 0.21/0.51  % (10971)------------------------------
% 0.21/0.51  % (10977)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (10975)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (10972)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (10970)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (10974)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (10992)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (10985)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (10991)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (10988)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (10984)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (10984)Refutation not found, incomplete strategy% (10984)------------------------------
% 0.21/0.52  % (10984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10984)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10984)Memory used [KB]: 1663
% 0.21/0.52  % (10984)Time elapsed: 0.083 s
% 0.21/0.52  % (10984)------------------------------
% 0.21/0.52  % (10984)------------------------------
% 0.21/0.52  % (10980)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (10980)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (10988)Refutation not found, incomplete strategy% (10988)------------------------------
% 0.21/0.53  % (10988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10988)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10988)Memory used [KB]: 1663
% 0.21/0.53  % (10988)Time elapsed: 0.118 s
% 0.21/0.53  % (10988)------------------------------
% 0.21/0.53  % (10988)------------------------------
% 0.21/0.53  % (10982)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f44,f49,f78,f82,f90,f114])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ~spl2_4 | spl2_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    $false | (~spl2_4 | spl2_5)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f89,f89,f89,f89,f76,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f18,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f17,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | ~spl2_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    spl2_4 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    k1_xboole_0 != sK0 | spl2_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl2_5 <=> k1_xboole_0 = sK0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ~spl2_5 | spl2_1 | ~spl2_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f84,f71,f41,f87])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    spl2_1 <=> sK0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    spl2_3 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    k1_xboole_0 != sK0 | (spl2_1 | ~spl2_3)),
% 0.21/0.53    inference(backward_demodulation,[],[f43,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f71])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    sK0 != sK1 | spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f41])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl2_1 | ~spl2_2 | spl2_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    $false | (spl2_1 | ~spl2_2 | spl2_4)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f43,f48,f77,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 | X2 = X5) )),
% 0.21/0.53    inference(definition_unfolding,[],[f25,f16,f16,f16])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.53    inference(flattening,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | spl2_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f75])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) | ~spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    spl2_2 <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    spl2_3 | ~spl2_4 | ~spl2_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f68,f46,f75,f71])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1 | ~spl2_2),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | ~spl2_2),
% 0.21/0.53    inference(superposition,[],[f32,f48])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    spl2_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f27,f46])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)),
% 0.21/0.53    inference(definition_unfolding,[],[f14,f26,f26])).
% 0.21/0.53  % (10995)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).
% 0.21/0.53  % (10998)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)) => (sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f7,plain,(
% 0.21/0.53    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.21/0.53    inference(negated_conjecture,[],[f5])).
% 0.21/0.53  fof(f5,conjecture,(
% 0.21/0.53    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ~spl2_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f15,f41])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    sK0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (10980)------------------------------
% 0.21/0.53  % (10980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10980)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (10980)Memory used [KB]: 10746
% 0.21/0.53  % (10980)Time elapsed: 0.125 s
% 0.21/0.53  % (10980)------------------------------
% 0.21/0.53  % (10980)------------------------------
% 0.21/0.53  % (10978)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (10983)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (10969)Success in time 0.174 s
%------------------------------------------------------------------------------
