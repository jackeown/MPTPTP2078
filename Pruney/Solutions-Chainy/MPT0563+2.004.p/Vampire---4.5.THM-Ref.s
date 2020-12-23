%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:03 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :   13
%              Number of atoms          :  160 ( 192 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f57])).

fof(f57,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f40,f55])).

fof(f55,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
        | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f51,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(X0,k1_relat_1(sK1)),k10_relat_1(sK1,X1))
        | r1_tarski(X0,k1_relat_1(sK1)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f50,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f49,f36])).

fof(f36,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f49,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK6(X0,X1,sK1)),sK1)
        | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f33,f44])).

% (6181)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f44,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl7_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
            & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
        & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f40,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl7_1
  <=> r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f45,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f41,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f25,f39])).

fof(f25,plain,(
    ~ r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:35:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (6170)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (6192)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (6184)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (6170)Refutation not found, incomplete strategy% (6170)------------------------------
% 0.21/0.52  % (6170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6170)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6170)Memory used [KB]: 1663
% 0.21/0.52  % (6170)Time elapsed: 0.103 s
% 0.21/0.52  % (6170)------------------------------
% 0.21/0.52  % (6170)------------------------------
% 0.21/0.53  % (6189)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (6192)Refutation not found, incomplete strategy% (6192)------------------------------
% 0.21/0.53  % (6192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6192)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6192)Memory used [KB]: 10618
% 0.21/0.53  % (6192)Time elapsed: 0.105 s
% 0.21/0.53  % (6192)------------------------------
% 0.21/0.53  % (6192)------------------------------
% 0.21/0.53  % (6180)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (6197)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.53  % (6191)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.25/0.53  % (6171)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.54  % (6189)Refutation found. Thanks to Tanya!
% 1.25/0.54  % SZS status Theorem for theBenchmark
% 1.25/0.54  % SZS output start Proof for theBenchmark
% 1.25/0.54  fof(f58,plain,(
% 1.25/0.54    $false),
% 1.25/0.54    inference(avatar_sat_refutation,[],[f41,f45,f57])).
% 1.25/0.54  fof(f57,plain,(
% 1.25/0.54    spl7_1 | ~spl7_2),
% 1.25/0.54    inference(avatar_contradiction_clause,[],[f56])).
% 1.25/0.54  fof(f56,plain,(
% 1.25/0.54    $false | (spl7_1 | ~spl7_2)),
% 1.25/0.54    inference(subsumption_resolution,[],[f40,f55])).
% 1.25/0.54  fof(f55,plain,(
% 1.25/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl7_2),
% 1.25/0.54    inference(duplicate_literal_removal,[],[f54])).
% 1.25/0.54  fof(f54,plain,(
% 1.25/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl7_2),
% 1.25/0.54    inference(resolution,[],[f51,f26])).
% 1.25/0.54  fof(f26,plain,(
% 1.25/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f13])).
% 1.25/0.54  fof(f13,plain,(
% 1.25/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f12])).
% 1.25/0.54  fof(f12,plain,(
% 1.25/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f8,plain,(
% 1.25/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.25/0.54    inference(ennf_transformation,[],[f6])).
% 1.25/0.54  fof(f6,plain,(
% 1.25/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.25/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 1.25/0.54  fof(f1,axiom,(
% 1.25/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.25/0.54  fof(f51,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~r2_hidden(sK2(X0,k1_relat_1(sK1)),k10_relat_1(sK1,X1)) | r1_tarski(X0,k1_relat_1(sK1))) ) | ~spl7_2),
% 1.25/0.54    inference(resolution,[],[f50,f27])).
% 1.25/0.54  fof(f27,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f13])).
% 1.25/0.54  fof(f50,plain,(
% 1.25/0.54    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) ) | ~spl7_2),
% 1.25/0.54    inference(resolution,[],[f49,f36])).
% 1.25/0.54  fof(f36,plain,(
% 1.25/0.54    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 1.25/0.54    inference(equality_resolution,[],[f29])).
% 1.25/0.54  fof(f29,plain,(
% 1.25/0.54    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.25/0.54    inference(cnf_transformation,[],[f19])).
% 1.25/0.54  fof(f19,plain,(
% 1.25/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).
% 1.25/0.54  fof(f16,plain,(
% 1.25/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f17,plain,(
% 1.25/0.54    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f18,plain,(
% 1.25/0.54    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f15,plain,(
% 1.25/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.25/0.54    inference(rectify,[],[f14])).
% 1.25/0.54  fof(f14,plain,(
% 1.25/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.25/0.54    inference(nnf_transformation,[],[f2])).
% 1.25/0.54  fof(f2,axiom,(
% 1.25/0.54    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.25/0.54  fof(f49,plain,(
% 1.25/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK6(X0,X1,sK1)),sK1) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) ) | ~spl7_2),
% 1.25/0.54    inference(resolution,[],[f33,f44])).
% 1.25/0.54  % (6181)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.25/0.54  fof(f44,plain,(
% 1.25/0.54    v1_relat_1(sK1) | ~spl7_2),
% 1.25/0.54    inference(avatar_component_clause,[],[f43])).
% 1.25/0.54  fof(f43,plain,(
% 1.25/0.54    spl7_2 <=> v1_relat_1(sK1)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.25/0.54  fof(f33,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f23])).
% 1.25/0.54  fof(f23,plain,(
% 1.25/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f22])).
% 1.25/0.54  fof(f22,plain,(
% 1.25/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f21,plain,(
% 1.25/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.25/0.54    inference(rectify,[],[f20])).
% 1.25/0.54  fof(f20,plain,(
% 1.25/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.25/0.54    inference(nnf_transformation,[],[f9])).
% 1.25/0.54  fof(f9,plain,(
% 1.25/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.25/0.54    inference(ennf_transformation,[],[f3])).
% 1.25/0.54  fof(f3,axiom,(
% 1.25/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 1.25/0.54  fof(f40,plain,(
% 1.25/0.54    ~r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) | spl7_1),
% 1.25/0.54    inference(avatar_component_clause,[],[f39])).
% 1.25/0.54  fof(f39,plain,(
% 1.25/0.54    spl7_1 <=> r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1))),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.25/0.54  fof(f45,plain,(
% 1.25/0.54    spl7_2),
% 1.25/0.54    inference(avatar_split_clause,[],[f24,f43])).
% 1.25/0.54  fof(f24,plain,(
% 1.25/0.54    v1_relat_1(sK1)),
% 1.25/0.54    inference(cnf_transformation,[],[f11])).
% 1.25/0.54  fof(f11,plain,(
% 1.25/0.54    ~r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).
% 1.25/0.54  fof(f10,plain,(
% 1.25/0.54    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f7,plain,(
% 1.25/0.54    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.25/0.54    inference(ennf_transformation,[],[f5])).
% 1.25/0.54  fof(f5,negated_conjecture,(
% 1.25/0.54    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.25/0.54    inference(negated_conjecture,[],[f4])).
% 1.25/0.54  fof(f4,conjecture,(
% 1.25/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.25/0.54  fof(f41,plain,(
% 1.25/0.54    ~spl7_1),
% 1.25/0.54    inference(avatar_split_clause,[],[f25,f39])).
% 1.25/0.54  fof(f25,plain,(
% 1.25/0.54    ~r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1))),
% 1.25/0.54    inference(cnf_transformation,[],[f11])).
% 1.25/0.54  % SZS output end Proof for theBenchmark
% 1.25/0.54  % (6189)------------------------------
% 1.25/0.54  % (6189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (6189)Termination reason: Refutation
% 1.25/0.54  
% 1.25/0.54  % (6189)Memory used [KB]: 10746
% 1.25/0.54  % (6189)Time elapsed: 0.117 s
% 1.25/0.54  % (6189)------------------------------
% 1.25/0.54  % (6189)------------------------------
% 1.25/0.54  % (6173)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.54  % (6196)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.25/0.54  % (6169)Success in time 0.175 s
%------------------------------------------------------------------------------
