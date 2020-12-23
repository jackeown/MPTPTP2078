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
% DateTime   : Thu Dec  3 12:58:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  82 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 258 expanded)
%              Number of equality atoms :   13 (  36 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f60,f71])).

fof(f71,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f69,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK0)
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f69,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(resolution,[],[f36,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f36,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_1
  <=> ! [X2] : ~ r2_hidden(X2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f60,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f58,f19])).

fof(f58,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_2 ),
    inference(resolution,[],[f53,f26])).

fof(f53,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f51,f43])).

fof(f43,plain,
    ( ~ r2_hidden(sK1(sK2(sK0),sK0),sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f40,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,sK2(X1)) ) ),
    inference(condensation,[],[f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK2(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f15])).

fof(f15,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f40,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_2
  <=> r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f51,plain,(
    ! [X2] :
      ( r2_hidden(sK1(sK2(sK0),sK0),sK0)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f29,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(sK1(X1,sK0),sK0) ) ),
    inference(resolution,[],[f20,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f20,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f32,f38,f35])).

fof(f32,plain,(
    ! [X2] :
      ( r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f28,f24])).

fof(f28,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK1(X0,sK0),X0) ) ),
    inference(resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:25:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (22489)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (22496)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (22496)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f41,f60,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ~spl4_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    $false | ~spl4_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f69,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    inference(negated_conjecture,[],[f4])).
% 0.21/0.52  fof(f4,conjecture,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl4_1),
% 0.21/0.52    inference(resolution,[],[f36,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | ~spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    spl4_1 <=> ! [X2] : ~r2_hidden(X2,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ~spl4_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    $false | ~spl4_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f58,f19])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl4_2),
% 0.21/0.52    inference(resolution,[],[f53,f26])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | ~spl4_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f51,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ~r2_hidden(sK1(sK2(sK0),sK0),sK0) | ~spl4_2),
% 0.21/0.52    inference(resolution,[],[f40,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,sK2(X1))) )),
% 0.21/0.52    inference(condensation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) | ~spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    spl4_2 <=> r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2] : (r2_hidden(sK1(sK2(sK0),sK0),sK0) | ~r2_hidden(X2,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f29,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(sK1(X1,sK0),sK0)) )),
% 0.21/0.52    inference(resolution,[],[f20,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    spl4_1 | spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f32,f38,f35])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2] : (r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) | ~r2_hidden(X2,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f28,f24])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK1(X0,sK0),X0)) )),
% 0.21/0.52    inference(resolution,[],[f20,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (22496)------------------------------
% 0.21/0.52  % (22496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22496)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (22496)Memory used [KB]: 6140
% 0.21/0.52  % (22496)Time elapsed: 0.105 s
% 0.21/0.52  % (22496)------------------------------
% 0.21/0.52  % (22496)------------------------------
% 0.21/0.52  % (22476)Success in time 0.164 s
%------------------------------------------------------------------------------
