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
% DateTime   : Thu Dec  3 13:07:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  54 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 160 expanded)
%              Number of equality atoms :   21 (  43 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f23,f28,f32,f37,f40])).

fof(f40,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f39])).

fof(f39,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f38,f17])).

fof(f17,plain,
    ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl3_1
  <=> k9_relat_1(sK0,sK2) = k9_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f38,plain,
    ( k9_relat_1(sK0,sK2) = k9_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f36,f27])).

fof(f27,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f36,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(k7_relat_1(X0,sK1),sK2) = k9_relat_1(X0,sK2) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_5
  <=> ! [X0] :
        ( k9_relat_1(k7_relat_1(X0,sK1),sK2) = k9_relat_1(X0,sK2)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f37,plain,
    ( spl3_5
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f33,f30,f20,f35])).

fof(f20,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f30,plain,
    ( spl3_4
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f33,plain,
    ( ! [X0] :
        ( k9_relat_1(k7_relat_1(X0,sK1),sK2) = k9_relat_1(X0,sK2)
        | ~ v1_relat_1(X0) )
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f31,f22])).

fof(f22,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f31,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X2)
        | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f30])).

fof(f32,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f13,f30])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f28,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f10,f25])).

fof(f10,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(sK2,sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8,f7])).

% (17533)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
fof(f7,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(X2,X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(sK0,X2) != k9_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(sK0,X2) != k9_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(X2,X1) )
   => ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X2,X1)
           => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X2,X1)
           => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X2,X1)
         => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_2)).

fof(f23,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f11,f20])).

fof(f11,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f12,f15])).

fof(f12,plain,(
    k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (17536)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.41  % (17536)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f18,f23,f28,f32,f37,f40])).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    spl3_1 | ~spl3_3 | ~spl3_5),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f39])).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    $false | (spl3_1 | ~spl3_3 | ~spl3_5)),
% 0.20/0.41    inference(subsumption_resolution,[],[f38,f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) | spl3_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    spl3_1 <=> k9_relat_1(sK0,sK2) = k9_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    k9_relat_1(sK0,sK2) = k9_relat_1(k7_relat_1(sK0,sK1),sK2) | (~spl3_3 | ~spl3_5)),
% 0.20/0.41    inference(resolution,[],[f36,f27])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    v1_relat_1(sK0) | ~spl3_3),
% 0.20/0.41    inference(avatar_component_clause,[],[f25])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    spl3_3 <=> v1_relat_1(sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(k7_relat_1(X0,sK1),sK2) = k9_relat_1(X0,sK2)) ) | ~spl3_5),
% 0.20/0.41    inference(avatar_component_clause,[],[f35])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    spl3_5 <=> ! [X0] : (k9_relat_1(k7_relat_1(X0,sK1),sK2) = k9_relat_1(X0,sK2) | ~v1_relat_1(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    spl3_5 | ~spl3_2 | ~spl3_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f33,f30,f20,f35])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    spl3_2 <=> r1_tarski(sK2,sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    spl3_4 <=> ! [X1,X0,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X0] : (k9_relat_1(k7_relat_1(X0,sK1),sK2) = k9_relat_1(X0,sK2) | ~v1_relat_1(X0)) ) | (~spl3_2 | ~spl3_4)),
% 0.20/0.41    inference(resolution,[],[f31,f22])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    r1_tarski(sK2,sK1) | ~spl3_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f20])).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~v1_relat_1(X0)) ) | ~spl3_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f30])).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    spl3_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f13,f30])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,plain,(
% 0.20/0.41    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    spl3_3),
% 0.20/0.41    inference(avatar_split_clause,[],[f10,f25])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    v1_relat_1(sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    (k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(sK2,sK1)) & v1_relat_1(sK0)),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8,f7])).
% 0.20/0.41  % (17533)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  fof(f7,plain,(
% 0.20/0.41    ? [X0] : (? [X1,X2] : (k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(X2,X1)) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(sK0,X2) != k9_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(X2,X1)) & v1_relat_1(sK0))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    ? [X2,X1] : (k9_relat_1(sK0,X2) != k9_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(X2,X1)) => (k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(sK2,sK1))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f5,plain,(
% 0.20/0.41    ? [X0] : (? [X1,X2] : (k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(X2,X1)) & v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,plain,(
% 0.20/0.41    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X2,X1) => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.20/0.41    inference(pure_predicate_removal,[],[f3])).
% 0.20/0.41  fof(f3,negated_conjecture,(
% 0.20/0.41    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(X2,X1) => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.20/0.41    inference(negated_conjecture,[],[f2])).
% 0.20/0.41  fof(f2,conjecture,(
% 0.20/0.41    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(X2,X1) => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_2)).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    spl3_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f11,f20])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    r1_tarski(sK2,sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f9])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ~spl3_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f12,f15])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.20/0.41    inference(cnf_transformation,[],[f9])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (17536)------------------------------
% 0.20/0.41  % (17536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (17536)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (17536)Memory used [KB]: 6012
% 0.20/0.41  % (17536)Time elapsed: 0.003 s
% 0.20/0.41  % (17536)------------------------------
% 0.20/0.41  % (17536)------------------------------
% 0.20/0.41  % (17534)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.41  % (17535)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.41  % (17525)Success in time 0.058 s
%------------------------------------------------------------------------------
