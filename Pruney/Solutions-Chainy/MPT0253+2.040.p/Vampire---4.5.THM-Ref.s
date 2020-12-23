%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:12 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 104 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  235 ( 569 expanded)
%              Number of equality atoms :   89 ( 158 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f326,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f237,f274,f325])).

fof(f325,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f323,f24])).

fof(f24,plain,(
    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

% (20518)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f323,plain,
    ( sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f303,f23])).

fof(f23,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f303,plain,
    ( ~ r2_hidden(sK2,sK1)
    | sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f302])).

fof(f302,plain,
    ( ~ r2_hidden(sK2,sK1)
    | sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ r2_hidden(sK2,sK1)
    | ~ spl5_4 ),
    inference(superposition,[],[f30,f236])).

fof(f236,plain,
    ( sK2 = sK3(k2_tarski(sK0,sK2),sK1,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl5_4
  <=> sK2 = sK3(k2_tarski(sK0,sK2),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f274,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f272,f24])).

fof(f272,plain,
    ( sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f252,f22])).

fof(f22,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f252,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f251])).

fof(f251,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ r2_hidden(sK0,sK1)
    | ~ spl5_3 ),
    inference(superposition,[],[f30,f232])).

fof(f232,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK2),sK1,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl5_3
  <=> sK0 = sK3(k2_tarski(sK0,sK2),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f237,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f223,f234,f230])).

fof(f223,plain,
    ( sK2 = sK3(k2_tarski(sK0,sK2),sK1,sK1)
    | sK0 = sK3(k2_tarski(sK0,sK2),sK1,sK1) ),
    inference(resolution,[],[f168,f44])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

% (20506)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f168,plain,(
    r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),k2_tarski(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f167,f128])).

fof(f128,plain,(
    ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,
    ( ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),sK1)
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),sK1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2] :
      ( sK1 != X2
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X2),sK1)
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X2),X2) ) ),
    inference(superposition,[],[f24,f30])).

fof(f167,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),sK1)
    | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),k2_tarski(sK0,sK2)) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),sK1)
    | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),k2_tarski(sK0,sK2))
    | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),sK1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X0),sK1)
      | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X0),k2_tarski(sK0,sK2))
      | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X0),X0) ) ),
    inference(superposition,[],[f24,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n001.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:32:59 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (20529)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (20512)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (20521)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (20511)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (20529)Refutation not found, incomplete strategy% (20529)------------------------------
% 0.22/0.53  % (20529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20529)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20529)Memory used [KB]: 1663
% 0.22/0.53  % (20529)Time elapsed: 0.115 s
% 0.22/0.53  % (20529)------------------------------
% 0.22/0.53  % (20529)------------------------------
% 0.22/0.53  % (20498)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (20499)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (20527)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (20526)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (20527)Refutation not found, incomplete strategy% (20527)------------------------------
% 0.22/0.54  % (20527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20527)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20527)Memory used [KB]: 6140
% 0.22/0.54  % (20527)Time elapsed: 0.138 s
% 0.22/0.54  % (20527)------------------------------
% 0.22/0.54  % (20527)------------------------------
% 0.22/0.54  % (20523)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (20502)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.42/0.55  % (20503)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.42/0.55  % (20501)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.42/0.55  % (20514)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.42/0.55  % (20504)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.42/0.55  % (20515)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.55  % (20519)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.55  % (20515)Refutation not found, incomplete strategy% (20515)------------------------------
% 1.42/0.55  % (20515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (20515)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (20515)Memory used [KB]: 10618
% 1.42/0.55  % (20515)Time elapsed: 0.146 s
% 1.42/0.55  % (20515)------------------------------
% 1.42/0.55  % (20515)------------------------------
% 1.42/0.55  % (20511)Refutation found. Thanks to Tanya!
% 1.42/0.55  % SZS status Theorem for theBenchmark
% 1.42/0.55  % SZS output start Proof for theBenchmark
% 1.42/0.55  fof(f326,plain,(
% 1.42/0.55    $false),
% 1.42/0.55    inference(avatar_sat_refutation,[],[f237,f274,f325])).
% 1.42/0.55  fof(f325,plain,(
% 1.42/0.55    ~spl5_4),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f324])).
% 1.42/0.55  fof(f324,plain,(
% 1.42/0.55    $false | ~spl5_4),
% 1.42/0.55    inference(subsumption_resolution,[],[f323,f24])).
% 1.42/0.55  fof(f24,plain,(
% 1.42/0.55    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f11])).
% 1.42/0.55  fof(f11,plain,(
% 1.42/0.55    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).
% 1.42/0.55  % (20518)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.55  fof(f10,plain,(
% 1.42/0.55    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f9,plain,(
% 1.42/0.55    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 1.42/0.55    inference(flattening,[],[f8])).
% 1.42/0.55  fof(f8,plain,(
% 1.42/0.55    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 1.42/0.55    inference(ennf_transformation,[],[f7])).
% 1.42/0.55  fof(f7,negated_conjecture,(
% 1.42/0.55    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.42/0.55    inference(negated_conjecture,[],[f6])).
% 1.42/0.55  fof(f6,conjecture,(
% 1.42/0.55    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 1.42/0.55  fof(f323,plain,(
% 1.42/0.55    sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1) | ~spl5_4),
% 1.42/0.55    inference(subsumption_resolution,[],[f303,f23])).
% 1.42/0.55  fof(f23,plain,(
% 1.42/0.55    r2_hidden(sK2,sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f11])).
% 1.42/0.55  fof(f303,plain,(
% 1.42/0.55    ~r2_hidden(sK2,sK1) | sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1) | ~spl5_4),
% 1.42/0.55    inference(duplicate_literal_removal,[],[f302])).
% 1.42/0.55  fof(f302,plain,(
% 1.42/0.55    ~r2_hidden(sK2,sK1) | sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1) | ~r2_hidden(sK2,sK1) | ~spl5_4),
% 1.42/0.55    inference(superposition,[],[f30,f236])).
% 1.42/0.55  fof(f236,plain,(
% 1.42/0.55    sK2 = sK3(k2_tarski(sK0,sK2),sK1,sK1) | ~spl5_4),
% 1.42/0.55    inference(avatar_component_clause,[],[f234])).
% 1.42/0.55  fof(f234,plain,(
% 1.42/0.55    spl5_4 <=> sK2 = sK3(k2_tarski(sK0,sK2),sK1,sK1)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.42/0.55  fof(f30,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f16])).
% 1.42/0.55  fof(f16,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).
% 1.42/0.55  fof(f15,plain,(
% 1.42/0.55    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f14,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.42/0.55    inference(rectify,[],[f13])).
% 1.42/0.55  fof(f13,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.42/0.55    inference(flattening,[],[f12])).
% 1.42/0.55  fof(f12,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.42/0.55    inference(nnf_transformation,[],[f1])).
% 1.42/0.55  fof(f1,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.42/0.55  fof(f274,plain,(
% 1.42/0.55    ~spl5_3),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f273])).
% 1.42/0.55  fof(f273,plain,(
% 1.42/0.55    $false | ~spl5_3),
% 1.42/0.55    inference(subsumption_resolution,[],[f272,f24])).
% 1.42/0.55  fof(f272,plain,(
% 1.42/0.55    sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1) | ~spl5_3),
% 1.42/0.55    inference(subsumption_resolution,[],[f252,f22])).
% 1.42/0.55  fof(f22,plain,(
% 1.42/0.55    r2_hidden(sK0,sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f11])).
% 1.42/0.55  fof(f252,plain,(
% 1.42/0.55    ~r2_hidden(sK0,sK1) | sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1) | ~spl5_3),
% 1.42/0.55    inference(duplicate_literal_removal,[],[f251])).
% 1.42/0.55  fof(f251,plain,(
% 1.42/0.55    ~r2_hidden(sK0,sK1) | sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1) | ~r2_hidden(sK0,sK1) | ~spl5_3),
% 1.42/0.55    inference(superposition,[],[f30,f232])).
% 1.42/0.55  fof(f232,plain,(
% 1.42/0.55    sK0 = sK3(k2_tarski(sK0,sK2),sK1,sK1) | ~spl5_3),
% 1.42/0.55    inference(avatar_component_clause,[],[f230])).
% 1.42/0.55  fof(f230,plain,(
% 1.42/0.55    spl5_3 <=> sK0 = sK3(k2_tarski(sK0,sK2),sK1,sK1)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.42/0.55  fof(f237,plain,(
% 1.42/0.55    spl5_3 | spl5_4),
% 1.42/0.55    inference(avatar_split_clause,[],[f223,f234,f230])).
% 1.42/0.55  fof(f223,plain,(
% 1.42/0.55    sK2 = sK3(k2_tarski(sK0,sK2),sK1,sK1) | sK0 = sK3(k2_tarski(sK0,sK2),sK1,sK1)),
% 1.42/0.55    inference(resolution,[],[f168,f44])).
% 1.42/0.55  fof(f44,plain,(
% 1.42/0.55    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 1.42/0.55    inference(equality_resolution,[],[f31])).
% 1.42/0.55  fof(f31,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.42/0.55    inference(cnf_transformation,[],[f21])).
% 1.42/0.55  fof(f21,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 1.42/0.55  fof(f20,plain,(
% 1.42/0.55    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f19,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.42/0.55    inference(rectify,[],[f18])).
% 1.42/0.55  fof(f18,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.42/0.55    inference(flattening,[],[f17])).
% 1.42/0.55  % (20506)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.42/0.55  fof(f17,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.42/0.55    inference(nnf_transformation,[],[f3])).
% 1.42/0.55  fof(f3,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.42/0.55  fof(f168,plain,(
% 1.42/0.55    r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),k2_tarski(sK0,sK2))),
% 1.42/0.55    inference(subsumption_resolution,[],[f167,f128])).
% 1.42/0.55  fof(f128,plain,(
% 1.42/0.55    ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),sK1)),
% 1.42/0.55    inference(duplicate_literal_removal,[],[f127])).
% 1.42/0.55  fof(f127,plain,(
% 1.42/0.55    ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),sK1) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),sK1)),
% 1.42/0.55    inference(equality_resolution,[],[f61])).
% 1.42/0.55  fof(f61,plain,(
% 1.42/0.55    ( ! [X2] : (sK1 != X2 | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X2),sK1) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X2),X2)) )),
% 1.42/0.55    inference(superposition,[],[f24,f30])).
% 1.42/0.55  fof(f167,plain,(
% 1.42/0.55    r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),sK1) | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),k2_tarski(sK0,sK2))),
% 1.42/0.55    inference(duplicate_literal_removal,[],[f166])).
% 1.42/0.55  fof(f166,plain,(
% 1.42/0.55    r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),sK1) | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),k2_tarski(sK0,sK2)) | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,sK1),sK1)),
% 1.42/0.55    inference(equality_resolution,[],[f59])).
% 1.42/0.55  fof(f59,plain,(
% 1.42/0.55    ( ! [X0] : (sK1 != X0 | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X0),sK1) | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X0),k2_tarski(sK0,sK2)) | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X0),X0)) )),
% 1.42/0.55    inference(superposition,[],[f24,f28])).
% 1.42/0.55  fof(f28,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f16])).
% 1.42/0.55  % SZS output end Proof for theBenchmark
% 1.42/0.55  % (20511)------------------------------
% 1.42/0.55  % (20511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (20511)Termination reason: Refutation
% 1.42/0.55  
% 1.42/0.55  % (20511)Memory used [KB]: 10874
% 1.42/0.55  % (20511)Time elapsed: 0.148 s
% 1.42/0.55  % (20511)------------------------------
% 1.42/0.55  % (20511)------------------------------
% 1.42/0.55  % (20518)Refutation not found, incomplete strategy% (20518)------------------------------
% 1.42/0.55  % (20518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (20518)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (20518)Memory used [KB]: 1663
% 1.42/0.55  % (20518)Time elapsed: 0.147 s
% 1.42/0.55  % (20518)------------------------------
% 1.42/0.55  % (20518)------------------------------
% 1.42/0.56  % (20509)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.42/0.56  % (20528)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.42/0.56  % (20510)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.42/0.56  % (20522)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.42/0.56  % (20508)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.56  % (20524)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.56  % (20520)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.56  % (20524)Refutation not found, incomplete strategy% (20524)------------------------------
% 1.42/0.56  % (20524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (20524)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (20524)Memory used [KB]: 10618
% 1.42/0.56  % (20524)Time elapsed: 0.160 s
% 1.42/0.56  % (20524)------------------------------
% 1.42/0.56  % (20524)------------------------------
% 1.42/0.57  % (20507)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.42/0.57  % (20497)Success in time 0.201 s
%------------------------------------------------------------------------------
