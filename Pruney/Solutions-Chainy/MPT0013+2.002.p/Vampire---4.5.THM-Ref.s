%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  56 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 353 expanded)
%              Number of equality atoms :   24 (  55 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f84,f89])).

fof(f89,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f85,f86])).

fof(f86,plain,
    ( ! [X0] : r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k2_xboole_0(sK0,X0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f83,f20])).

fof(f20,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f10])).

fof(f10,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f83,plain,
    ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_2
  <=> r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f85,plain,
    ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f25,f83,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl3_1
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f84,plain,
    ( spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f52,f23,f81])).

fof(f52,plain,
    ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),sK0)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f25,f50])).

% (16348)Refutation not found, incomplete strategy% (16348)------------------------------
% (16348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f46,f18])).

% (16348)Termination reason: Refutation not found, incomplete strategy

% (16348)Memory used [KB]: 6012
% (16348)Time elapsed: 0.064 s
% (16348)------------------------------
% (16348)------------------------------
fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X1),X1)
      | r2_hidden(sK2(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f12,f23])).

fof(f12,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k2_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (16355)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (16348)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (16355)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f26,f84,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl3_1 | ~spl3_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    $false | (spl3_1 | ~spl3_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f85,f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k2_xboole_0(sK0,X0))) ) | ~spl3_2),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f83,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(rectify,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),sK0) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl3_2 <=> r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1)) | (spl3_1 | ~spl3_2)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f25,f83,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    spl3_1 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl3_2 | spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f52,f23,f81])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),sK0) | spl3_1),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f25,f50])).
% 0.21/0.47  % (16348)Refutation not found, incomplete strategy% (16348)------------------------------
% 0.21/0.47  % (16348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f46,f18])).
% 0.21/0.47  % (16348)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (16348)Memory used [KB]: 6012
% 0.21/0.47  % (16348)Time elapsed: 0.064 s
% 0.21/0.47  % (16348)------------------------------
% 0.21/0.47  % (16348)------------------------------
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X1),X1) | r2_hidden(sK2(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.47    inference(factoring,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f12,f23])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f5])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k2_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f4,plain,(
% 0.21/0.47    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f2])).
% 0.21/0.47  fof(f2,conjecture,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (16355)------------------------------
% 0.21/0.47  % (16355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (16355)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (16355)Memory used [KB]: 1663
% 0.21/0.47  % (16355)Time elapsed: 0.057 s
% 0.21/0.47  % (16355)------------------------------
% 0.21/0.47  % (16355)------------------------------
% 0.21/0.47  % (16347)Success in time 0.117 s
%------------------------------------------------------------------------------
