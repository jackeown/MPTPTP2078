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
% DateTime   : Thu Dec  3 12:53:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  87 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  159 ( 275 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f38,f42,f49,f53,f58,f67])).

fof(f67,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7 ),
    inference(subsumption_resolution,[],[f64,f57])).

fof(f57,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_7
  <=> r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f64,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f63,f37])).

fof(f37,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,X0)) )
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f62,f28])).

fof(f28,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f62,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(sK0,X0)
        | r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,X0)) )
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f59,f41])).

fof(f41,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_4
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(sK0,X0)
        | r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,X0)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f48,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f48,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_5
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f58,plain,
    ( ~ spl4_7
    | ~ spl4_1
    | spl4_6 ),
    inference(avatar_split_clause,[],[f54,f51,f27,f56])).

fof(f51,plain,
    ( spl4_6
  <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f54,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl4_1
    | spl4_6 ),
    inference(forward_demodulation,[],[f52,f34])).

fof(f34,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl4_1 ),
    inference(resolution,[],[f28,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
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

fof(f52,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f53,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f16,f51])).

fof(f16,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r2_hidden(X0,X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
         => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X0,X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
       => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

fof(f49,plain,
    ( spl4_5
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f45,f40,f31,f27,f47])).

fof(f31,plain,
    ( spl4_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f45,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f44,f28])).

fof(f44,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f43,f32])).

fof(f32,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f43,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f41,f25])).

fof(f25,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f42,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f14,f40])).

fof(f14,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f15,f36])).

fof(f15,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f13,f31])).

fof(f13,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f29,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f12,f27])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:02:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (2412)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.46  % (2412)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f68,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f29,f33,f38,f42,f49,f53,f58,f67])).
% 0.22/0.46  fof(f67,plain,(
% 0.22/0.46    ~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_7),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f66])).
% 0.22/0.46  fof(f66,plain,(
% 0.22/0.46    $false | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_7)),
% 0.22/0.46    inference(subsumption_resolution,[],[f64,f57])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    ~r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1)) | spl4_7),
% 0.22/0.46    inference(avatar_component_clause,[],[f56])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    spl4_7 <=> r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.46  fof(f64,plain,(
% 0.22/0.46    r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1)) | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.46    inference(resolution,[],[f63,f37])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    r2_hidden(sK0,sK1) | ~spl4_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f36])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    spl4_3 <=> r2_hidden(sK0,sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.46  fof(f63,plain,(
% 0.22/0.46    ( ! [X0] : (~r2_hidden(sK0,X0) | r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,X0))) ) | (~spl4_1 | ~spl4_4 | ~spl4_5)),
% 0.22/0.46    inference(subsumption_resolution,[],[f62,f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    v1_relat_1(sK2) | ~spl4_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    spl4_1 <=> v1_relat_1(sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.46  fof(f62,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_relat_1(sK2) | ~r2_hidden(sK0,X0) | r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,X0))) ) | (~spl4_4 | ~spl4_5)),
% 0.22/0.46    inference(subsumption_resolution,[],[f59,f41])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl4_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f40])).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    spl4_4 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    ( ! [X0] : (~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(sK0,X0) | r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,X0))) ) | ~spl4_5),
% 0.22/0.46    inference(resolution,[],[f48,f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.46    inference(ennf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~spl4_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f47])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    spl4_5 <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.46  fof(f58,plain,(
% 0.22/0.46    ~spl4_7 | ~spl4_1 | spl4_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f54,f51,f27,f56])).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    spl4_6 <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    ~r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1)) | (~spl4_1 | spl4_6)),
% 0.22/0.46    inference(forward_demodulation,[],[f52,f34])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | ~spl4_1),
% 0.22/0.46    inference(resolution,[],[f28,f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,plain,(
% 0.22/0.46    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) | spl4_6),
% 0.22/0.46    inference(avatar_component_clause,[],[f51])).
% 0.22/0.46  fof(f53,plain,(
% 0.22/0.46    ~spl4_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f16,f51])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,plain,(
% 0.22/0.46    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.46    inference(flattening,[],[f6])).
% 0.22/0.46  fof(f6,plain,(
% 0.22/0.46    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & (r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.22/0.46    inference(negated_conjecture,[],[f4])).
% 0.22/0.46  fof(f4,conjecture,(
% 0.22/0.46    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    spl4_5 | ~spl4_1 | ~spl4_2 | ~spl4_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f45,f40,f31,f27,f47])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    spl4_2 <=> v1_funct_1(sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.22/0.46    inference(subsumption_resolution,[],[f44,f28])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | (~spl4_2 | ~spl4_4)),
% 0.22/0.46    inference(subsumption_resolution,[],[f43,f32])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    v1_funct_1(sK2) | ~spl4_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f31])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~spl4_4),
% 0.22/0.46    inference(resolution,[],[f41,f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ( ! [X2,X0] : (~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.22/0.46    inference(equality_resolution,[],[f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.46    inference(flattening,[],[f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    spl4_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f14,f40])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    spl4_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f15,f36])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    r2_hidden(sK0,sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    spl4_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f13,f31])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    v1_funct_1(sK2)),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    spl4_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f12,f27])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    v1_relat_1(sK2)),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (2412)------------------------------
% 0.22/0.46  % (2412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (2412)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (2412)Memory used [KB]: 6140
% 0.22/0.46  % (2412)Time elapsed: 0.009 s
% 0.22/0.46  % (2412)------------------------------
% 0.22/0.46  % (2412)------------------------------
% 0.22/0.47  % (2411)Success in time 0.103 s
%------------------------------------------------------------------------------
