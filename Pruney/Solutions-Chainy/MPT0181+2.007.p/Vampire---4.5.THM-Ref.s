%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 125 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  219 ( 932 expanded)
%              Number of equality atoms :  147 ( 703 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f275,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f172,f219,f274])).

fof(f274,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f272,f13])).

fof(f13,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f4,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(f272,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f262,f23])).

fof(f23,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).

fof(f11,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f262,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2))
    | k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1)
    | ~ spl4_8 ),
    inference(trivial_inequality_removal,[],[f259])).

fof(f259,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2))
    | k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1)
    | sK2 != sK2
    | ~ spl4_8 ),
    inference(superposition,[],[f20,f139])).

fof(f139,plain,
    ( sK2 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_8
  <=> sK2 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X1
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f219,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f217,f13])).

fof(f217,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f207,f27])).

fof(f27,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f207,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))
    | k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1)
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f202])).

fof(f202,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))
    | k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1)
    | sK0 != sK0
    | ~ spl4_7 ),
    inference(superposition,[],[f19,f135])).

fof(f135,plain,
    ( sK0 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl4_7
  <=> sK0 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f172,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f170,f13])).

fof(f170,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f160,f25])).

fof(f25,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k1_enumset1(X0,X5,X2)) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f160,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2))
    | k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f159])).

fof(f159,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2))
    | k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1)
    | sK1 != sK1
    | ~ spl4_6 ),
    inference(superposition,[],[f21,f131])).

fof(f131,plain,
    ( sK1 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl4_6
  <=> sK1 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f140,plain,
    ( spl4_6
    | spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f127,f137,f133,f129])).

fof(f127,plain,
    ( sK2 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( sK2 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))
    | sK2 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X8,X7] :
      ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(X6,X7,X8)
      | sK2 = sK3(sK0,sK2,sK1,k1_enumset1(X6,X7,X8))
      | sK0 = sK3(sK0,sK2,sK1,k1_enumset1(X6,X7,X8))
      | sK1 = sK3(sK0,sK2,sK1,k1_enumset1(X6,X7,X8))
      | sK3(sK0,sK2,sK1,k1_enumset1(X6,X7,X8)) = X8
      | sK3(sK0,sK2,sK1,k1_enumset1(X6,X7,X8)) = X7
      | sK3(sK0,sK2,sK1,k1_enumset1(X6,X7,X8)) = X6 ) ),
    inference(resolution,[],[f29,f28])).

fof(f28,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,sK2,sK1,X0),X0)
      | sK1 = sK3(sK0,sK2,sK1,X0)
      | sK2 = sK3(sK0,sK2,sK1,X0)
      | sK0 = sK3(sK0,sK2,sK1,X0)
      | k1_enumset1(sK0,sK1,sK2) != X0 ) ),
    inference(superposition,[],[f13,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) = X2
      | sK3(X0,X1,X2,X3) = X1
      | sK3(X0,X1,X2,X3) = X0
      | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (32410)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.45  % (32426)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.45  % (32418)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.46  % (32415)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (32422)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (32412)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (32418)Refutation not found, incomplete strategy% (32418)------------------------------
% 0.21/0.47  % (32418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (32418)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (32418)Memory used [KB]: 6012
% 0.21/0.47  % (32418)Time elapsed: 0.086 s
% 0.21/0.47  % (32418)------------------------------
% 0.21/0.47  % (32418)------------------------------
% 0.21/0.47  % (32409)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (32423)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (32423)Refutation not found, incomplete strategy% (32423)------------------------------
% 0.21/0.47  % (32423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (32423)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (32423)Memory used [KB]: 6140
% 0.21/0.47  % (32423)Time elapsed: 0.071 s
% 0.21/0.47  % (32423)------------------------------
% 0.21/0.47  % (32423)------------------------------
% 0.21/0.48  % (32424)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (32413)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (32411)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (32420)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (32411)Refutation not found, incomplete strategy% (32411)------------------------------
% 0.21/0.49  % (32411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32411)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32411)Memory used [KB]: 10490
% 0.21/0.49  % (32411)Time elapsed: 0.088 s
% 0.21/0.49  % (32411)------------------------------
% 0.21/0.49  % (32411)------------------------------
% 0.21/0.49  % (32420)Refutation not found, incomplete strategy% (32420)------------------------------
% 0.21/0.49  % (32420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32420)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32420)Memory used [KB]: 6140
% 0.21/0.49  % (32420)Time elapsed: 0.086 s
% 0.21/0.49  % (32420)------------------------------
% 0.21/0.49  % (32420)------------------------------
% 0.21/0.49  % (32417)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (32408)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (32408)Refutation not found, incomplete strategy% (32408)------------------------------
% 0.21/0.49  % (32408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32408)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32408)Memory used [KB]: 6012
% 0.21/0.49  % (32408)Time elapsed: 0.084 s
% 0.21/0.49  % (32408)------------------------------
% 0.21/0.49  % (32408)------------------------------
% 0.21/0.49  % (32409)Refutation not found, incomplete strategy% (32409)------------------------------
% 0.21/0.49  % (32409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32409)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32409)Memory used [KB]: 10490
% 0.21/0.49  % (32409)Time elapsed: 0.083 s
% 0.21/0.49  % (32409)------------------------------
% 0.21/0.49  % (32409)------------------------------
% 0.21/0.49  % (32427)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (32425)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (32428)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (32428)Refutation not found, incomplete strategy% (32428)------------------------------
% 0.21/0.49  % (32428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32428)Memory used [KB]: 10490
% 0.21/0.49  % (32428)Time elapsed: 0.096 s
% 0.21/0.49  % (32428)------------------------------
% 0.21/0.49  % (32428)------------------------------
% 0.21/0.50  % (32427)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f140,f172,f219,f274])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    ~spl4_8),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f273])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    $false | ~spl4_8),
% 0.21/0.50    inference(subsumption_resolution,[],[f272,f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f4,f6])).
% 0.21/0.50  fof(f6,plain,(
% 0.21/0.50    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1) => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f4,plain,(
% 0.21/0.50    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1)),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 0.21/0.50    inference(negated_conjecture,[],[f2])).
% 0.21/0.50  fof(f2,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1) | ~spl4_8),
% 0.21/0.50    inference(subsumption_resolution,[],[f262,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 0.21/0.50    inference(equality_resolution,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 0.21/0.50    inference(equality_resolution,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.50    inference(rectify,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.50    inference(flattening,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.50    inference(nnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    ~r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2)) | k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1) | ~spl4_8),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f259])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    ~r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2)) | k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1) | sK2 != sK2 | ~spl4_8),
% 0.21/0.50    inference(superposition,[],[f20,f139])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    sK2 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) | ~spl4_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    spl4_8 <=> sK2 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X1 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    ~spl4_7),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f218])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    $false | ~spl4_7),
% 0.21/0.50    inference(subsumption_resolution,[],[f217,f13])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1) | ~spl4_7),
% 0.21/0.50    inference(subsumption_resolution,[],[f207,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 0.21/0.50    inference(equality_resolution,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 0.21/0.50    inference(equality_resolution,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ~r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2)) | k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1) | ~spl4_7),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f202])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    ~r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2)) | k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1) | sK0 != sK0 | ~spl4_7),
% 0.21/0.50    inference(superposition,[],[f19,f135])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    sK0 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) | ~spl4_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f133])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    spl4_7 <=> sK0 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X0 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ~spl4_6),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    $false | ~spl4_6),
% 0.21/0.50    inference(subsumption_resolution,[],[f170,f13])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1) | ~spl4_6),
% 0.21/0.50    inference(subsumption_resolution,[],[f160,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X2,X0,X5] : (r2_hidden(X5,k1_enumset1(X0,X5,X2))) )),
% 0.21/0.50    inference(equality_resolution,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k1_enumset1(X0,X5,X2) != X3) )),
% 0.21/0.50    inference(equality_resolution,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ~r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2)) | k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1) | ~spl4_6),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f159])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ~r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2)) | k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK0,sK2,sK1) | sK1 != sK1 | ~spl4_6),
% 0.21/0.50    inference(superposition,[],[f21,f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    sK1 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) | ~spl4_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f129])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    spl4_6 <=> sK1 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X2 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl4_6 | spl4_7 | spl4_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f127,f137,f133,f129])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    sK2 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) | sK1 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f126])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    sK2 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) | sK1 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) | sK2 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) | sK1 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK0,sK2,sK1,k1_enumset1(sK0,sK1,sK2))),
% 0.21/0.50    inference(equality_resolution,[],[f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X6,X8,X7] : (k1_enumset1(sK0,sK1,sK2) != k1_enumset1(X6,X7,X8) | sK2 = sK3(sK0,sK2,sK1,k1_enumset1(X6,X7,X8)) | sK0 = sK3(sK0,sK2,sK1,k1_enumset1(X6,X7,X8)) | sK1 = sK3(sK0,sK2,sK1,k1_enumset1(X6,X7,X8)) | sK3(sK0,sK2,sK1,k1_enumset1(X6,X7,X8)) = X8 | sK3(sK0,sK2,sK1,k1_enumset1(X6,X7,X8)) = X7 | sK3(sK0,sK2,sK1,k1_enumset1(X6,X7,X8)) = X6) )),
% 0.21/0.50    inference(resolution,[],[f29,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.50    inference(equality_resolution,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK3(sK0,sK2,sK1,X0),X0) | sK1 = sK3(sK0,sK2,sK1,X0) | sK2 = sK3(sK0,sK2,sK1,X0) | sK0 = sK3(sK0,sK2,sK1,X0) | k1_enumset1(sK0,sK1,sK2) != X0) )),
% 0.21/0.50    inference(superposition,[],[f13,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (32427)------------------------------
% 0.21/0.50  % (32427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32427)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (32427)Memory used [KB]: 6268
% 0.21/0.50  % (32427)Time elapsed: 0.094 s
% 0.21/0.50  % (32427)------------------------------
% 0.21/0.50  % (32427)------------------------------
% 0.21/0.50  % (32404)Success in time 0.147 s
%------------------------------------------------------------------------------
