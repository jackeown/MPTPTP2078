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
% DateTime   : Thu Dec  3 12:41:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 124 expanded)
%              Number of leaves         :   11 (  52 expanded)
%              Depth                    :    6
%              Number of atoms          :  103 ( 341 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f23,f34,f35,f40,f45,f55,f60,f61,f62,f67])).

fof(f67,plain,
    ( spl4_8
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f46,f37,f20,f64])).

fof(f64,plain,
    ( spl4_8
  <=> r2_hidden(k4_tarski(sK1,k4_tarski(sK0,sK1)),k2_zfmisc_1(sK3,k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f20,plain,
    ( spl4_2
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f37,plain,
    ( spl4_4
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f46,plain,
    ( r2_hidden(k4_tarski(sK1,k4_tarski(sK0,sK1)),k2_zfmisc_1(sK3,k2_zfmisc_1(sK2,sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f22,f39,f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f39,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f22,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f62,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f47,f37,f52])).

fof(f52,plain,
    ( spl4_6
  <=> r2_hidden(k4_tarski(sK1,sK1),k2_zfmisc_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f47,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),k2_zfmisc_1(sK3,sK3))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f39,f39,f13])).

fof(f61,plain,
    ( ~ spl4_5
    | spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f48,f37,f15,f42])).

fof(f42,plain,
    ( spl4_5
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f15,plain,
    ( spl4_1
  <=> r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f48,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl4_1
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f17,f39,f13])).

fof(f17,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f60,plain,
    ( spl4_7
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f49,f37,f20,f57])).

fof(f57,plain,
    ( spl4_7
  <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK1),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f49,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK1),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK3))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f22,f39,f13])).

fof(f55,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f50,f37,f52])).

fof(f50,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),k2_zfmisc_1(sK3,sK3))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f39,f39,f13])).

fof(f45,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f26,f20,f42])).

fof(f26,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f22,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f27,f20,f37])).

fof(f27,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f22,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f28,f20,f31])).

fof(f31,plain,
    ( spl4_3
  <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f28,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f22,f22,f13])).

fof(f34,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f29,f20,f31])).

fof(f29,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f22,f22,f13])).

fof(f23,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f9,f20])).

fof(f9,plain,(
    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    & r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2))
        & r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ~ r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2))
      & r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2))
      & r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
       => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
     => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_zfmisc_1)).

fof(f18,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f10,f15])).

fof(f10,plain,(
    ~ r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (8081)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (8081)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f18,f23,f34,f35,f40,f45,f55,f60,f61,f62,f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    spl4_8 | ~spl4_2 | ~spl4_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f46,f37,f20,f64])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    spl4_8 <=> r2_hidden(k4_tarski(sK1,k4_tarski(sK0,sK1)),k2_zfmisc_1(sK3,k2_zfmisc_1(sK2,sK3)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    spl4_2 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    spl4_4 <=> r2_hidden(sK1,sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(sK1,k4_tarski(sK0,sK1)),k2_zfmisc_1(sK3,k2_zfmisc_1(sK2,sK3))) | (~spl4_2 | ~spl4_4)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f22,f39,f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.46    inference(flattening,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.46    inference(nnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    r2_hidden(sK1,sK3) | ~spl4_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f37])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f20])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    spl4_6 | ~spl4_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f47,f37,f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    spl4_6 <=> r2_hidden(k4_tarski(sK1,sK1),k2_zfmisc_1(sK3,sK3))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(sK1,sK1),k2_zfmisc_1(sK3,sK3)) | ~spl4_4),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f39,f39,f13])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    ~spl4_5 | spl4_1 | ~spl4_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f48,f37,f15,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    spl4_5 <=> r2_hidden(sK0,sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    spl4_1 <=> r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ~r2_hidden(sK0,sK2) | (spl4_1 | ~spl4_4)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f17,f39,f13])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ~r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | spl4_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f15])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    spl4_7 | ~spl4_2 | ~spl4_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f49,f37,f20,f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    spl4_7 <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK1),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK3))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK1),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK3)) | (~spl4_2 | ~spl4_4)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f22,f39,f13])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    spl4_6 | ~spl4_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f50,f37,f52])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(sK1,sK1),k2_zfmisc_1(sK3,sK3)) | ~spl4_4),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f39,f39,f13])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    spl4_5 | ~spl4_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f20,f42])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    r2_hidden(sK0,sK2) | ~spl4_2),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f22,f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    spl4_4 | ~spl4_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f27,f20,f37])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    r2_hidden(sK1,sK3) | ~spl4_2),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f22,f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    spl4_3 | ~spl4_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f28,f20,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    spl4_3 <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3))) | ~spl4_2),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f22,f22,f13])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    spl4_3 | ~spl4_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f29,f20,f31])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3))) | ~spl4_2),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f22,f22,f13])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    spl4_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f9,f20])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,plain,(
% 0.20/0.46    ~r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2)) & r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f4,f5])).
% 0.20/0.46  fof(f5,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) & r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) => (~r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2)) & r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f4,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) & r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)))),
% 0.20/0.46    inference(negated_conjecture,[],[f2])).
% 0.20/0.46  fof(f2,conjecture,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_zfmisc_1)).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ~spl4_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f10,f15])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ~r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (8081)------------------------------
% 0.20/0.46  % (8081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (8081)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (8081)Memory used [KB]: 5373
% 0.20/0.46  % (8081)Time elapsed: 0.058 s
% 0.20/0.46  % (8081)------------------------------
% 0.20/0.46  % (8081)------------------------------
% 0.20/0.47  % (8067)Success in time 0.11 s
%------------------------------------------------------------------------------
