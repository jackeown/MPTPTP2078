%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 152 expanded)
%              Number of leaves         :   10 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  161 ( 573 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f63,f78])).

fof(f78,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f76,f36])).

fof(f36,plain,(
    v1_ordinal1(sK1) ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r2_hidden(sK1,sK0)
    & ~ r1_ordinal1(sK0,sK1)
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(X1,X0)
            & ~ r1_ordinal1(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(X1,sK0)
          & ~ r1_ordinal1(sK0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ~ r2_hidden(X1,sK0)
        & ~ r1_ordinal1(sK0,X1)
        & v3_ordinal1(X1) )
   => ( ~ r2_hidden(sK1,sK0)
      & ~ r1_ordinal1(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
              | r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f76,plain,
    ( ~ v1_ordinal1(sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f75,f25])).

fof(f25,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ v1_ordinal1(sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f74,f28])).

fof(f28,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v1_ordinal1(sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f51,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f51,plain,
    ( r2_xboole_0(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_1
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f63,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f60,f57])).

fof(f57,plain,
    ( r1_ordinal1(sK0,sK0)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f41,f54])).

fof(f54,plain,
    ( sK0 = sK1
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f41,plain,(
    r1_ordinal1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f40,f26])).

fof(f40,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f37,f25])).

fof(f37,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f31,f27])).

fof(f27,plain,(
    ~ r1_ordinal1(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f60,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f27,f54])).

fof(f55,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f48,f53,f50])).

fof(f48,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f46,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f46,plain,(
    r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f45,f26])).

fof(f45,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f44,f25])).

fof(f44,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:43:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.43  % (31804)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.44  % (31804)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % (31819)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f79,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f55,f63,f78])).
% 0.20/0.44  fof(f78,plain,(
% 0.20/0.44    ~spl2_1),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f77])).
% 0.20/0.44  fof(f77,plain,(
% 0.20/0.44    $false | ~spl2_1),
% 0.20/0.44    inference(subsumption_resolution,[],[f76,f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    v1_ordinal1(sK1)),
% 0.20/0.44    inference(resolution,[],[f30,f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    v3_ordinal1(sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    (~r2_hidden(sK1,sK0) & ~r1_ordinal1(sK0,sK1) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f22,f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (~r2_hidden(X1,X0) & ~r1_ordinal1(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (~r2_hidden(X1,sK0) & ~r1_ordinal1(sK0,X1) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ? [X1] : (~r2_hidden(X1,sK0) & ~r1_ordinal1(sK0,X1) & v3_ordinal1(X1)) => (~r2_hidden(sK1,sK0) & ~r1_ordinal1(sK0,sK1) & v3_ordinal1(sK1))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (~r2_hidden(X1,X0) & ~r1_ordinal1(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.44    inference(flattening,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : ((~r2_hidden(X1,X0) & ~r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,negated_conjecture,(
% 0.20/0.44    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.44    inference(negated_conjecture,[],[f6])).
% 0.20/0.44  fof(f6,conjecture,(
% 0.20/0.44    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 0.20/0.44    inference(pure_predicate_removal,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.20/0.44  fof(f76,plain,(
% 0.20/0.44    ~v1_ordinal1(sK1) | ~spl2_1),
% 0.20/0.44    inference(subsumption_resolution,[],[f75,f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    v3_ordinal1(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    ~v3_ordinal1(sK0) | ~v1_ordinal1(sK1) | ~spl2_1),
% 0.20/0.44    inference(subsumption_resolution,[],[f74,f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ~r2_hidden(sK1,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~v1_ordinal1(sK1) | ~spl2_1),
% 0.20/0.44    inference(resolution,[],[f51,f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.20/0.44    inference(flattening,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    r2_xboole_0(sK1,sK0) | ~spl2_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f50])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    spl2_1 <=> r2_xboole_0(sK1,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    ~spl2_2),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f62])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    $false | ~spl2_2),
% 0.20/0.44    inference(subsumption_resolution,[],[f60,f57])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    r1_ordinal1(sK0,sK0) | ~spl2_2),
% 0.20/0.44    inference(backward_demodulation,[],[f41,f54])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    sK0 = sK1 | ~spl2_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f53])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    spl2_2 <=> sK0 = sK1),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    r1_ordinal1(sK1,sK0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f40,f26])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f37,f25])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.20/0.44    inference(resolution,[],[f31,f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ~r1_ordinal1(sK0,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.44    inference(flattening,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    ~r1_ordinal1(sK0,sK0) | ~spl2_2),
% 0.20/0.44    inference(backward_demodulation,[],[f27,f54])).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    spl2_1 | spl2_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f48,f53,f50])).
% 0.20/0.44  fof(f48,plain,(
% 0.20/0.44    sK0 = sK1 | r2_xboole_0(sK1,sK0)),
% 0.20/0.44    inference(resolution,[],[f46,f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(flattening,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.20/0.44    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    r1_tarski(sK1,sK0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f45,f26])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f44,f25])).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.20/0.44    inference(resolution,[],[f41,f32])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.44    inference(nnf_transformation,[],[f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.44    inference(flattening,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (31804)------------------------------
% 0.20/0.44  % (31804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (31804)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (31804)Memory used [KB]: 10618
% 0.20/0.44  % (31804)Time elapsed: 0.056 s
% 0.20/0.44  % (31804)------------------------------
% 0.20/0.44  % (31804)------------------------------
% 0.20/0.44  % (31801)Success in time 0.096 s
%------------------------------------------------------------------------------
