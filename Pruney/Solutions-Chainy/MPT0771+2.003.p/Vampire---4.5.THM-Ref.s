%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  72 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 200 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f37,f43])).

fof(f43,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f42])).

fof(f42,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f41,f23])).

fof(f23,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl3_1
  <=> r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f41,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | spl3_1 ),
    inference(resolution,[],[f40,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f7,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
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

fof(f40,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)),k3_relat_1(k2_wellord1(sK1,X0)))
    | spl3_1 ),
    inference(resolution,[],[f39,f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_relat_1(sK1))
      | ~ r2_hidden(sK2(X0,k3_relat_1(sK1)),k3_relat_1(k2_wellord1(sK1,X1))) ) ),
    inference(resolution,[],[f38,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_relat_1(sK1))
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(sK1,X1))) ) ),
    inference(resolution,[],[f18,f14])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
      | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(f37,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f36])).

fof(f36,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_2
  <=> r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0) ),
    inference(duplicate_literal_removal,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0)
      | r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f32,f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,X0)),X1),X0)
      | r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X1) ) ),
    inference(resolution,[],[f31,f16])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(sK1,X1)))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f19,f14])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f15,f25,f21])).

fof(f15,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
    | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:16:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (15552)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.47  % (15552)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f28,f37,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl3_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    $false | spl3_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f41,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    spl3_1 <=> r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) | spl3_1),
% 0.21/0.47    inference(resolution,[],[f40,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f7,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)),k3_relat_1(k2_wellord1(sK1,X0)))) ) | spl3_1),
% 0.21/0.47    inference(resolution,[],[f39,f23])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_relat_1(sK1)) | ~r2_hidden(sK2(X0,k3_relat_1(sK1)),k3_relat_1(k2_wellord1(sK1,X1)))) )),
% 0.21/0.47    inference(resolution,[],[f38,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X0,k3_relat_1(sK1)) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(sK1,X1)))) )),
% 0.21/0.47    inference(resolution,[],[f18,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    (~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) | ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1] : ((~r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) & v1_relat_1(X1)) => ((~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) | ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1] : ((~r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 0.21/0.47    inference(negated_conjecture,[],[f3])).
% 0.21/0.47  fof(f3,conjecture,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | r2_hidden(X0,k3_relat_1(X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    $false | spl3_2),
% 0.21/0.47    inference(resolution,[],[f35,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) | spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    spl3_2 <=> r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0) | r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0)) )),
% 0.21/0.47    inference(resolution,[],[f32,f17])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,X0)),X1),X0) | r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X1)) )),
% 0.21/0.47    inference(resolution,[],[f31,f16])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(sK1,X1))) | r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(resolution,[],[f19,f14])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ~spl3_1 | ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f15,f25,f21])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) | ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (15552)------------------------------
% 0.21/0.47  % (15552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (15552)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (15552)Memory used [KB]: 5373
% 0.21/0.47  % (15552)Time elapsed: 0.063 s
% 0.21/0.47  % (15552)------------------------------
% 0.21/0.47  % (15552)------------------------------
% 0.21/0.48  % (15551)Success in time 0.119 s
%------------------------------------------------------------------------------
