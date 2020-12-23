%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  98 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  192 ( 454 expanded)
%              Number of equality atoms :   28 (  70 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f50,f82])).

fof(f82,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f80,f27])).

fof(f27,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f80,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f79,f31])).

fof(f31,plain,
    ( k1_xboole_0 != k3_relat_1(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl3_1
  <=> k1_xboole_0 = k3_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f79,plain,
    ( k1_xboole_0 = k3_relat_1(sK0)
    | ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f76,f48])).

fof(f48,plain,
    ( r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_4
  <=> r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f76,plain,
    ( ~ r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))
    | k1_xboole_0 = k3_relat_1(sK0)
    | ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,
    ( ~ r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))
    | k1_xboole_0 = k3_relat_1(sK0)
    | ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | ~ r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f73,f19])).

fof(f19,plain,(
    ! [X1] :
      ( r2_hidden(sK1(X1),k3_relat_1(sK0))
      | ~ r2_hidden(X1,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ! [X1] :
        ( ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
          & r2_hidden(sK1(X1),k3_relat_1(sK0)) )
        | ~ r2_hidden(X1,k3_relat_1(sK0)) )
    & k1_xboole_0 != k3_relat_1(sK0)
    & v2_wellord1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f10,f9])).

fof(f9,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
        & k3_relat_1(X0) != k1_xboole_0
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
              & r2_hidden(X2,k3_relat_1(sK0)) )
          | ~ r2_hidden(X1,k3_relat_1(sK0)) )
      & k1_xboole_0 != k3_relat_1(sK0)
      & v2_wellord1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
          & r2_hidden(X2,k3_relat_1(sK0)) )
     => ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
        & r2_hidden(sK1(X1),k3_relat_1(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),X0)
              & r2_hidden(X2,k3_relat_1(X0)) )
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      & k3_relat_1(X0) != k1_xboole_0
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),X0)
              & r2_hidden(X2,k3_relat_1(X0)) )
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      & k3_relat_1(X0) != k1_xboole_0
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ~ ( ! [X1] :
                ~ ( ! [X2] :
                      ( r2_hidden(X2,k3_relat_1(X0))
                     => r2_hidden(k4_tarski(X1,X2),X0) )
                  & r2_hidden(X1,k3_relat_1(X0)) )
            & k3_relat_1(X0) != k1_xboole_0
            & v2_wellord1(X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ~ ( ! [X1] :
              ~ ( ! [X2] :
                    ( r2_hidden(X2,k3_relat_1(X0))
                   => r2_hidden(k4_tarski(X1,X2),X0) )
                & r2_hidden(X1,k3_relat_1(X0)) )
          & k3_relat_1(X0) != k1_xboole_0
          & v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord1)).

fof(f73,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(sK2(sK0,X0)),X0)
        | ~ r2_hidden(sK2(sK0,X0),k3_relat_1(sK0))
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k3_relat_1(sK0)) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f72,f41])).

fof(f41,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK0,X0),k3_relat_1(sK0))
        | ~ r2_hidden(sK1(sK2(sK0,X0)),X0)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k3_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f66,f36])).

fof(f36,plain,
    ( v2_wellord1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_2
  <=> v2_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f66,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK0,X0),k3_relat_1(sK0))
      | ~ r2_hidden(sK1(sK2(sK0,X0)),X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | ~ v2_wellord1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f20,f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
      | ~ r2_hidden(X3,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X3] :
                ( r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(sK2(X0,X1),X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord1)).

fof(f20,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
      | ~ r2_hidden(X1,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,
    ( spl3_4
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f43,f39,f34,f29,f46])).

fof(f43,plain,
    ( r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f41,f36,f27,f31,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f29])).

fof(f18,plain,(
    k1_xboole_0 != k3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:49:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (8428)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.45  % (8421)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.46  % (8428)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f32,f37,f42,f50,f82])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f81])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.46    inference(subsumption_resolution,[],[f80,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.46    inference(equality_resolution,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.46    inference(subsumption_resolution,[],[f79,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    k1_xboole_0 != k3_relat_1(sK0) | spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    spl3_1 <=> k1_xboole_0 = k3_relat_1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    k1_xboole_0 = k3_relat_1(sK0) | ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.46    inference(subsumption_resolution,[],[f76,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl3_4 <=> r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    ~r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) | k1_xboole_0 = k3_relat_1(sK0) | ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | (~spl3_2 | ~spl3_3)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ~r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) | k1_xboole_0 = k3_relat_1(sK0) | ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | ~r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) | (~spl3_2 | ~spl3_3)),
% 0.21/0.46    inference(resolution,[],[f73,f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X1] : (r2_hidden(sK1(X1),k3_relat_1(sK0)) | ~r2_hidden(X1,k3_relat_1(sK0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X1] : ((~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) & r2_hidden(sK1(X1),k3_relat_1(sK0))) | ~r2_hidden(X1,k3_relat_1(sK0))) & k1_xboole_0 != k3_relat_1(sK0) & v2_wellord1(sK0) & v1_relat_1(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f10,f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0] : (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0) & v1_relat_1(X0)) => (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),sK0) & r2_hidden(X2,k3_relat_1(sK0))) | ~r2_hidden(X1,k3_relat_1(sK0))) & k1_xboole_0 != k3_relat_1(sK0) & v2_wellord1(sK0) & v1_relat_1(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),sK0) & r2_hidden(X2,k3_relat_1(sK0))) => (~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) & r2_hidden(sK1(X1),k3_relat_1(sK0))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0] : (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0) & v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f5])).
% 0.21/0.46  fof(f5,plain,(
% 0.21/0.46    ? [X0] : ((! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)) & v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (v1_relat_1(X0) => ~(! [X1] : ~(! [X2] : (r2_hidden(X2,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X2),X0)) & r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)))),
% 0.21/0.46    inference(negated_conjecture,[],[f3])).
% 0.21/0.46  fof(f3,conjecture,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ~(! [X1] : ~(! [X2] : (r2_hidden(X2,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X2),X0)) & r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord1)).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(sK1(sK2(sK0,X0)),X0) | ~r2_hidden(sK2(sK0,X0),k3_relat_1(sK0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_relat_1(sK0))) ) | (~spl3_2 | ~spl3_3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f72,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    v1_relat_1(sK0) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    spl3_3 <=> v1_relat_1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(sK2(sK0,X0),k3_relat_1(sK0)) | ~r2_hidden(sK1(sK2(sK0,X0)),X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_relat_1(sK0)) | ~v1_relat_1(sK0)) ) | ~spl3_2),
% 0.21/0.46    inference(subsumption_resolution,[],[f66,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    v2_wellord1(sK0) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl3_2 <=> v2_wellord1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(sK2(sK0,X0),k3_relat_1(sK0)) | ~r2_hidden(sK1(sK2(sK0,X0)),X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_relat_1(sK0)) | ~v2_wellord1(sK0) | ~v1_relat_1(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f20,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(X3,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((! [X3] : (r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X1)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ! [X0] : ((! [X1] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(! [X2] : ~(! [X3] : (r2_hidden(X3,X1) => r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X2,X1)) & k1_xboole_0 != X1 & r1_tarski(X1,k3_relat_1(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord1)).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) | ~r2_hidden(X1,k3_relat_1(sK0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl3_4 | spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f43,f39,f34,f29,f46])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f41,f36,f27,f31,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f16,f39])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    v1_relat_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f34])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    v2_wellord1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ~spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f18,f29])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    k1_xboole_0 != k3_relat_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (8428)------------------------------
% 0.21/0.46  % (8428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (8428)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (8428)Memory used [KB]: 6140
% 0.21/0.46  % (8428)Time elapsed: 0.065 s
% 0.21/0.46  % (8428)------------------------------
% 0.21/0.46  % (8428)------------------------------
% 0.21/0.46  % (8414)Success in time 0.101 s
%------------------------------------------------------------------------------
