%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 (  97 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  217 ( 431 expanded)
%              Number of equality atoms :   91 ( 182 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f327,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f159,f169,f174,f200,f309,f325,f326])).

fof(f326,plain,
    ( k1_xboole_0 != np__1
    | v1_xboole_0(np__1)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f325,plain,
    ( spl7_1
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | spl7_1
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f322,f158])).

fof(f158,plain,
    ( k1_xboole_0 != sK0
    | spl7_1 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f322,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_12 ),
    inference(resolution,[],[f303,f81])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f303,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl7_12
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f309,plain,
    ( spl7_12
    | spl7_13
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f299,f197,f305,f302])).

fof(f305,plain,
    ( spl7_13
  <=> k1_xboole_0 = np__1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f197,plain,
    ( spl7_5
  <=> sK1(sK0) = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f299,plain,
    ( ! [X0] :
        ( k1_xboole_0 = np__1
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_5 ),
    inference(duplicate_literal_removal,[],[f298])).

fof(f298,plain,
    ( ! [X0] :
        ( k1_xboole_0 = np__1
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_5 ),
    inference(superposition,[],[f80,f296])).

fof(f296,plain,
    ( ! [X0] :
        ( np__1 = k1_funct_1(sK1(sK0),X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_5 ),
    inference(superposition,[],[f89,f199])).

fof(f199,plain,
    ( sK1(sK0) = sK3(sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f197])).

fof(f89,plain,(
    ! [X2,X0] :
      ( np__1 = k1_funct_1(sK3(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( np__1 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f80,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK1(X0)) = X0
      & v1_funct_1(sK1(X0))
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK1(X0)) = X0
        & v1_funct_1(sK1(X0))
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f200,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f195,f197])).

fof(f195,plain,(
    sK1(sK0) = sK3(sK0) ),
    inference(equality_resolution,[],[f194])).

fof(f194,plain,(
    ! [X0] :
      ( sK0 != X0
      | sK3(X0) = sK1(sK0) ) ),
    inference(equality_resolution,[],[f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( sK0 != X1
      | sK3(X0) = sK1(X1)
      | sK0 != X0 ) ),
    inference(subsumption_resolution,[],[f187,f86])).

fof(f86,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f61])).

fof(f187,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK3(X0) = sK1(X1)
      | sK0 != X1
      | ~ v1_relat_1(sK3(X0)) ) ),
    inference(subsumption_resolution,[],[f185,f87])).

fof(f87,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f61])).

fof(f185,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK3(X0) = sK1(X1)
      | sK0 != X1
      | ~ v1_funct_1(sK3(X0))
      | ~ v1_relat_1(sK3(X0)) ) ),
    inference(superposition,[],[f177,f88])).

fof(f88,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

fof(f177,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != sK0
      | sK1(X0) = X1
      | sK0 != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f176,f77])).

fof(f77,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f57])).

fof(f176,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK1(X0) = X1
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(sK1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f175,f78])).

fof(f78,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f57])).

fof(f175,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK1(X0) = X1
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(sK1(X0))
      | ~ v1_relat_1(sK1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f75,f79])).

fof(f79,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

fof(f75,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | X1 = X2
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( k1_xboole_0 != sK0
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK0
            | k1_relat_1(X1) != sK0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f54])).

fof(f54,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK0
              | k1_relat_1(X1) != sK0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f34])).

% (21830)Refutation not found, incomplete strategy% (21830)------------------------------
% (21830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21830)Termination reason: Refutation not found, incomplete strategy

% (21830)Memory used [KB]: 6268
% (21830)Time elapsed: 0.120 s
% (21830)------------------------------
% (21830)------------------------------
% (21825)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (21818)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f34,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(f174,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f132,f171])).

% (21826)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f171,plain,
    ( spl7_4
  <=> v1_xboole_0(np__1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f132,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',spc1_boole)).

fof(f169,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f85,f166])).

fof(f166,plain,
    ( spl7_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f85,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f159,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f76,f156])).

fof(f76,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:15:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (21805)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (21809)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (21822)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (21807)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (21821)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (21830)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (21821)Refutation not found, incomplete strategy% (21821)------------------------------
% 0.21/0.52  % (21821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21821)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21821)Memory used [KB]: 1663
% 0.21/0.52  % (21821)Time elapsed: 0.110 s
% 0.21/0.52  % (21821)------------------------------
% 0.21/0.52  % (21821)------------------------------
% 0.21/0.52  % (21829)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (21816)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (21817)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (21813)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (21829)Refutation not found, incomplete strategy% (21829)------------------------------
% 0.21/0.53  % (21829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21810)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (21824)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (21829)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21829)Memory used [KB]: 6268
% 0.21/0.53  % (21829)Time elapsed: 0.110 s
% 0.21/0.53  % (21829)------------------------------
% 0.21/0.53  % (21829)------------------------------
% 0.21/0.53  % (21814)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (21806)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (21808)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (21811)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (21824)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f327,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f159,f169,f174,f200,f309,f325,f326])).
% 0.21/0.53  fof(f326,plain,(
% 0.21/0.53    k1_xboole_0 != np__1 | v1_xboole_0(np__1) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.53  fof(f325,plain,(
% 0.21/0.53    spl7_1 | ~spl7_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f324])).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    $false | (spl7_1 | ~spl7_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f322,f158])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    k1_xboole_0 != sK0 | spl7_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f156])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    spl7_1 <=> k1_xboole_0 = sK0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.53  fof(f322,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | ~spl7_12),
% 0.21/0.53    inference(resolution,[],[f303,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.53  fof(f303,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl7_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f302])).
% 0.21/0.53  fof(f302,plain,(
% 0.21/0.53    spl7_12 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.53  fof(f309,plain,(
% 0.21/0.53    spl7_12 | spl7_13 | ~spl7_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f299,f197,f305,f302])).
% 0.21/0.53  fof(f305,plain,(
% 0.21/0.53    spl7_13 <=> k1_xboole_0 = np__1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    spl7_5 <=> sK1(sK0) = sK3(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.53  fof(f299,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = np__1 | ~r2_hidden(X0,sK0)) ) | ~spl7_5),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f298])).
% 0.21/0.53  fof(f298,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = np__1 | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK0)) ) | ~spl7_5),
% 0.21/0.53    inference(superposition,[],[f80,f296])).
% 0.21/0.53  fof(f296,plain,(
% 0.21/0.53    ( ! [X0] : (np__1 = k1_funct_1(sK1(sK0),X0) | ~r2_hidden(X0,sK0)) ) | ~spl7_5),
% 0.21/0.53    inference(superposition,[],[f89,f199])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    sK1(sK0) = sK3(sK0) | ~spl7_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f197])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X2,X0] : (np__1 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ! [X0] : (! [X2] : (np__1 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (np__1 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,axiom,(
% 0.21/0.53    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,axiom,(
% 0.21/0.53    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    spl7_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f195,f197])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    sK1(sK0) = sK3(sK0)),
% 0.21/0.53    inference(equality_resolution,[],[f194])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    ( ! [X0] : (sK0 != X0 | sK3(X0) = sK1(sK0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f188])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK0 != X1 | sK3(X0) = sK1(X1) | sK0 != X0) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f187,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f61])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK0 != X0 | sK3(X0) = sK1(X1) | sK0 != X1 | ~v1_relat_1(sK3(X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f185,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f61])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK0 != X0 | sK3(X0) = sK1(X1) | sK0 != X1 | ~v1_funct_1(sK3(X0)) | ~v1_relat_1(sK3(X0))) )),
% 0.21/0.53    inference(superposition,[],[f177,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f61])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_relat_1(X1) != sK0 | sK1(X0) = X1 | sK0 != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f176,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f57])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK0 != X0 | sK1(X0) = X1 | k1_relat_1(X1) != sK0 | ~v1_relat_1(sK1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f175,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f57])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK0 != X0 | sK1(X0) = X1 | k1_relat_1(X1) != sK0 | ~v1_funct_1(sK1(X0)) | ~v1_relat_1(sK1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(superposition,[],[f75,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f57])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | X1 = X2 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(flattening,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.53    inference(negated_conjecture,[],[f34])).
% 0.21/0.53  % (21830)Refutation not found, incomplete strategy% (21830)------------------------------
% 0.21/0.53  % (21830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21830)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21830)Memory used [KB]: 6268
% 0.21/0.53  % (21830)Time elapsed: 0.120 s
% 0.21/0.53  % (21830)------------------------------
% 0.21/0.53  % (21830)------------------------------
% 0.21/0.54  % (21825)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (21818)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  fof(f34,conjecture,(
% 0.21/0.54    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    ~spl7_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f132,f171])).
% 0.21/0.54  % (21826)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    spl7_4 <=> v1_xboole_0(np__1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ~v1_xboole_0(np__1)),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,axiom,(
% 0.21/0.54    ~v1_xboole_0(np__1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',spc1_boole)).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f85,f166])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    spl7_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ~spl7_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f76,f156])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    k1_xboole_0 != sK0),
% 0.21/0.54    inference(cnf_transformation,[],[f55])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (21824)------------------------------
% 0.21/0.54  % (21824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21824)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (21824)Memory used [KB]: 6396
% 0.21/0.54  % (21824)Time elapsed: 0.125 s
% 0.21/0.54  % (21824)------------------------------
% 0.21/0.54  % (21824)------------------------------
% 0.21/0.55  % (21799)Success in time 0.179 s
%------------------------------------------------------------------------------
