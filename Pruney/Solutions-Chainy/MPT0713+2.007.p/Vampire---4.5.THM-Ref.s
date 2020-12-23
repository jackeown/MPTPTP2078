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
% DateTime   : Thu Dec  3 12:54:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  79 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  150 ( 265 expanded)
%              Number of equality atoms :   29 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f34,f39,f43,f47,f53,f63])).

fof(f63,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f23,f61])).

fof(f61,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f49,f60])).

fof(f60,plain,
    ( k1_tarski(k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k1_tarski(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f59,f42])).

fof(f42,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_5
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f59,plain,
    ( k1_tarski(k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_tarski(sK0,sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f54,f42])).

fof(f54,plain,
    ( k9_relat_1(sK1,k2_tarski(sK0,sK0)) = k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f23,f28,f33,f33,f52])).

fof(f52,plain,
    ( ! [X2,X0,X1] :
        ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
        | ~ r2_hidden(X1,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_7
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
        | ~ r2_hidden(X1,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f33,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_3
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f28,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f49,plain,
    ( k1_tarski(k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f38,f46])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f38,plain,
    ( k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_4
  <=> k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) = k1_tarski(k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f23,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f53,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f19,f51])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(f47,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f43,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f17,f41])).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0))
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) != k1_tarski(k1_funct_1(X1,X0))
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0))
      & r2_hidden(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

fof(f34,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f13,f21])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:53:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.40  % (25336)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.40  % (25336)Refutation found. Thanks to Tanya!
% 0.20/0.40  % SZS status Theorem for theBenchmark
% 0.20/0.40  % SZS output start Proof for theBenchmark
% 0.20/0.40  fof(f66,plain,(
% 0.20/0.40    $false),
% 0.20/0.40    inference(avatar_sat_refutation,[],[f24,f29,f34,f39,f43,f47,f53,f63])).
% 0.20/0.40  fof(f63,plain,(
% 0.20/0.40    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_7),
% 0.20/0.40    inference(avatar_contradiction_clause,[],[f62])).
% 0.20/0.40  fof(f62,plain,(
% 0.20/0.40    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_7)),
% 0.20/0.40    inference(subsumption_resolution,[],[f23,f61])).
% 0.20/0.40  fof(f61,plain,(
% 0.20/0.40    ~v1_relat_1(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_7)),
% 0.20/0.40    inference(subsumption_resolution,[],[f49,f60])).
% 0.20/0.40  fof(f60,plain,(
% 0.20/0.40    k1_tarski(k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k1_tarski(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7)),
% 0.20/0.40    inference(forward_demodulation,[],[f59,f42])).
% 0.20/0.40  fof(f42,plain,(
% 0.20/0.40    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl2_5),
% 0.20/0.40    inference(avatar_component_clause,[],[f41])).
% 0.20/0.40  fof(f41,plain,(
% 0.20/0.40    spl2_5 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.40  fof(f59,plain,(
% 0.20/0.40    k1_tarski(k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_tarski(sK0,sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7)),
% 0.20/0.40    inference(forward_demodulation,[],[f54,f42])).
% 0.20/0.40  fof(f54,plain,(
% 0.20/0.40    k9_relat_1(sK1,k2_tarski(sK0,sK0)) = k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_7)),
% 0.20/0.40    inference(unit_resulting_resolution,[],[f23,f28,f33,f33,f52])).
% 0.20/0.40  fof(f52,plain,(
% 0.20/0.40    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl2_7),
% 0.20/0.40    inference(avatar_component_clause,[],[f51])).
% 0.20/0.40  fof(f51,plain,(
% 0.20/0.40    spl2_7 <=> ! [X1,X0,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.40  fof(f33,plain,(
% 0.20/0.40    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl2_3),
% 0.20/0.40    inference(avatar_component_clause,[],[f31])).
% 0.20/0.40  fof(f31,plain,(
% 0.20/0.40    spl2_3 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.40  fof(f28,plain,(
% 0.20/0.40    v1_funct_1(sK1) | ~spl2_2),
% 0.20/0.40    inference(avatar_component_clause,[],[f26])).
% 0.20/0.40  fof(f26,plain,(
% 0.20/0.40    spl2_2 <=> v1_funct_1(sK1)),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.40  fof(f49,plain,(
% 0.20/0.40    k1_tarski(k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k1_tarski(sK0)) | ~v1_relat_1(sK1) | (spl2_4 | ~spl2_6)),
% 0.20/0.40    inference(superposition,[],[f38,f46])).
% 0.20/0.40  fof(f46,plain,(
% 0.20/0.40    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl2_6),
% 0.20/0.40    inference(avatar_component_clause,[],[f45])).
% 0.20/0.40  fof(f45,plain,(
% 0.20/0.40    spl2_6 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.40  fof(f38,plain,(
% 0.20/0.40    k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0)) | spl2_4),
% 0.20/0.40    inference(avatar_component_clause,[],[f36])).
% 0.20/0.40  fof(f36,plain,(
% 0.20/0.40    spl2_4 <=> k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) = k1_tarski(k1_funct_1(sK1,sK0))),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.40  fof(f23,plain,(
% 0.20/0.40    v1_relat_1(sK1) | ~spl2_1),
% 0.20/0.40    inference(avatar_component_clause,[],[f21])).
% 0.20/0.40  fof(f21,plain,(
% 0.20/0.40    spl2_1 <=> v1_relat_1(sK1)),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.40  fof(f53,plain,(
% 0.20/0.40    spl2_7),
% 0.20/0.40    inference(avatar_split_clause,[],[f19,f51])).
% 0.20/0.40  fof(f19,plain,(
% 0.20/0.40    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f10])).
% 0.20/0.40  fof(f10,plain,(
% 0.20/0.40    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.40    inference(flattening,[],[f9])).
% 0.20/0.40  fof(f9,plain,(
% 0.20/0.40    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.40    inference(ennf_transformation,[],[f3])).
% 0.20/0.40  fof(f3,axiom,(
% 0.20/0.40    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).
% 0.20/0.40  fof(f47,plain,(
% 0.20/0.40    spl2_6),
% 0.20/0.40    inference(avatar_split_clause,[],[f18,f45])).
% 0.20/0.40  fof(f18,plain,(
% 0.20/0.40    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f8])).
% 0.20/0.40  fof(f8,plain,(
% 0.20/0.40    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.40    inference(ennf_transformation,[],[f2])).
% 0.20/0.40  fof(f2,axiom,(
% 0.20/0.40    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.40  fof(f43,plain,(
% 0.20/0.40    spl2_5),
% 0.20/0.40    inference(avatar_split_clause,[],[f17,f41])).
% 0.20/0.40  fof(f17,plain,(
% 0.20/0.40    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f1])).
% 0.20/0.40  fof(f1,axiom,(
% 0.20/0.40    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.40  fof(f39,plain,(
% 0.20/0.40    ~spl2_4),
% 0.20/0.40    inference(avatar_split_clause,[],[f16,f36])).
% 0.20/0.40  fof(f16,plain,(
% 0.20/0.40    k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.20/0.40    inference(cnf_transformation,[],[f12])).
% 0.20/0.40  fof(f12,plain,(
% 0.20/0.40    k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f11])).
% 0.20/0.40  fof(f11,plain,(
% 0.20/0.40    ? [X0,X1] : (k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.40    introduced(choice_axiom,[])).
% 0.20/0.40  fof(f7,plain,(
% 0.20/0.40    ? [X0,X1] : (k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.40    inference(flattening,[],[f6])).
% 0.20/0.40  fof(f6,plain,(
% 0.20/0.40    ? [X0,X1] : ((k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.40    inference(ennf_transformation,[],[f5])).
% 0.20/0.40  fof(f5,negated_conjecture,(
% 0.20/0.40    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.40    inference(negated_conjecture,[],[f4])).
% 0.20/0.40  fof(f4,conjecture,(
% 0.20/0.40    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).
% 0.20/0.40  fof(f34,plain,(
% 0.20/0.40    spl2_3),
% 0.20/0.40    inference(avatar_split_clause,[],[f15,f31])).
% 0.20/0.40  fof(f15,plain,(
% 0.20/0.40    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.40    inference(cnf_transformation,[],[f12])).
% 0.20/0.40  fof(f29,plain,(
% 0.20/0.40    spl2_2),
% 0.20/0.40    inference(avatar_split_clause,[],[f14,f26])).
% 0.20/0.40  fof(f14,plain,(
% 0.20/0.40    v1_funct_1(sK1)),
% 0.20/0.40    inference(cnf_transformation,[],[f12])).
% 0.20/0.40  fof(f24,plain,(
% 0.20/0.40    spl2_1),
% 0.20/0.40    inference(avatar_split_clause,[],[f13,f21])).
% 0.20/0.40  fof(f13,plain,(
% 0.20/0.40    v1_relat_1(sK1)),
% 0.20/0.40    inference(cnf_transformation,[],[f12])).
% 0.20/0.40  % SZS output end Proof for theBenchmark
% 0.20/0.40  % (25336)------------------------------
% 0.20/0.40  % (25336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.40  % (25336)Termination reason: Refutation
% 0.20/0.40  
% 0.20/0.40  % (25336)Memory used [KB]: 6140
% 0.20/0.40  % (25336)Time elapsed: 0.028 s
% 0.20/0.40  % (25336)------------------------------
% 0.20/0.40  % (25336)------------------------------
% 0.20/0.40  % (25330)Success in time 0.059 s
%------------------------------------------------------------------------------
