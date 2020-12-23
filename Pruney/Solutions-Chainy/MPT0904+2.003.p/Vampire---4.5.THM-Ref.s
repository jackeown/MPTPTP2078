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
% DateTime   : Thu Dec  3 12:59:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  78 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :  100 ( 208 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f45,f58,f60,f68,f76])).

fof(f76,plain,
    ( ~ spl8_1
    | spl8_6 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | ~ spl8_1
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f43,f70,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f70,plain,
    ( ! [X0,X1] : r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK4,X1))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f18,f12])).

fof(f18,plain,
    ( r1_xboole_0(sK0,sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl8_1
  <=> r1_xboole_0(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f43,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl8_6
  <=> r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f68,plain,
    ( ~ spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f47,f33,f28])).

fof(f28,plain,
    ( spl8_4
  <=> r1_xboole_0(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f33,plain,
    ( spl8_5
  <=> r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f47,plain,
    ( ~ r1_xboole_0(sK3,sK7)
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f35,f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f33])).

fof(f60,plain,
    ( ~ spl8_3
    | spl8_6 ),
    inference(avatar_split_clause,[],[f53,f41,f24])).

fof(f24,plain,
    ( spl8_3
  <=> r1_xboole_0(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f53,plain,
    ( ~ r1_xboole_0(sK2,sK6)
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f43,f13])).

fof(f58,plain,
    ( ~ spl8_2
    | spl8_6 ),
    inference(avatar_contradiction_clause,[],[f55])).

fof(f55,plain,
    ( $false
    | ~ spl8_2
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f46,f43,f12])).

fof(f46,plain,
    ( ! [X0,X1] : r1_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK5))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f22,f13])).

fof(f22,plain,
    ( r1_xboole_0(sK1,sK5)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl8_2
  <=> r1_xboole_0(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f45,plain,
    ( ~ spl8_6
    | spl8_5 ),
    inference(avatar_split_clause,[],[f39,f33,f41])).

fof(f39,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl8_5 ),
    inference(resolution,[],[f12,f35])).

fof(f36,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f14,f33])).

fof(f14,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f9,f11,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f9,plain,(
    ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ( r1_xboole_0(sK3,sK7)
      | r1_xboole_0(sK2,sK6)
      | r1_xboole_0(sK1,sK5)
      | r1_xboole_0(sK0,sK4) )
    & ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( r1_xboole_0(X3,X7)
          | r1_xboole_0(X2,X6)
          | r1_xboole_0(X1,X5)
          | r1_xboole_0(X0,X4) )
        & ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
   => ( ( r1_xboole_0(sK3,sK7)
        | r1_xboole_0(sK2,sK6)
        | r1_xboole_0(sK1,sK5)
        | r1_xboole_0(sK0,sK4) )
      & ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( r1_xboole_0(X3,X7)
        | r1_xboole_0(X2,X6)
        | r1_xboole_0(X1,X5)
        | r1_xboole_0(X0,X4) )
      & ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
       => ( ~ r1_xboole_0(X3,X7)
          & ~ r1_xboole_0(X2,X6)
          & ~ r1_xboole_0(X1,X5)
          & ~ r1_xboole_0(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
     => ( ~ r1_xboole_0(X3,X7)
        & ~ r1_xboole_0(X2,X6)
        & ~ r1_xboole_0(X1,X5)
        & ~ r1_xboole_0(X0,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_mcart_1)).

fof(f31,plain,
    ( spl8_1
    | spl8_2
    | spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f10,f28,f24,f20,f16])).

fof(f10,plain,
    ( r1_xboole_0(sK3,sK7)
    | r1_xboole_0(sK2,sK6)
    | r1_xboole_0(sK1,sK5)
    | r1_xboole_0(sK0,sK4) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:10:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (16981)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.43  % (16981)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f31,f36,f45,f58,f60,f68,f76])).
% 0.22/0.43  fof(f76,plain,(
% 0.22/0.43    ~spl8_1 | spl8_6),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f75])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    $false | (~spl8_1 | spl8_6)),
% 0.22/0.43    inference(unit_resulting_resolution,[],[f43,f70,f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,plain,(
% 0.22/0.43    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK4,X1))) ) | ~spl8_1),
% 0.22/0.43    inference(unit_resulting_resolution,[],[f18,f12])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    r1_xboole_0(sK0,sK4) | ~spl8_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    spl8_1 <=> r1_xboole_0(sK0,sK4)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ~r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | spl8_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f41])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    spl8_6 <=> r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    ~spl8_4 | spl8_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f47,f33,f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    spl8_4 <=> r1_xboole_0(sK3,sK7)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    spl8_5 <=> r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ~r1_xboole_0(sK3,sK7) | spl8_5),
% 0.22/0.43    inference(unit_resulting_resolution,[],[f35,f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ~r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | spl8_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f33])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    ~spl8_3 | spl8_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f53,f41,f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    spl8_3 <=> r1_xboole_0(sK2,sK6)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    ~r1_xboole_0(sK2,sK6) | spl8_6),
% 0.22/0.43    inference(unit_resulting_resolution,[],[f43,f13])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    ~spl8_2 | spl8_6),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f55])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    $false | (~spl8_2 | spl8_6)),
% 0.22/0.43    inference(unit_resulting_resolution,[],[f46,f43,f12])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK5))) ) | ~spl8_2),
% 0.22/0.43    inference(unit_resulting_resolution,[],[f22,f13])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    r1_xboole_0(sK1,sK5) | ~spl8_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    spl8_2 <=> r1_xboole_0(sK1,sK5)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    ~spl8_6 | spl8_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f39,f33,f41])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    ~r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | spl8_5),
% 0.22/0.43    inference(resolution,[],[f12,f35])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ~spl8_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f14,f33])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ~r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.22/0.43    inference(definition_unfolding,[],[f9,f11,f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ~r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    (r1_xboole_0(sK3,sK7) | r1_xboole_0(sK2,sK6) | r1_xboole_0(sK1,sK5) | r1_xboole_0(sK0,sK4)) & ~r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f5,f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((r1_xboole_0(X3,X7) | r1_xboole_0(X2,X6) | r1_xboole_0(X1,X5) | r1_xboole_0(X0,X4)) & ~r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) => ((r1_xboole_0(sK3,sK7) | r1_xboole_0(sK2,sK6) | r1_xboole_0(sK1,sK5) | r1_xboole_0(sK0,sK4)) & ~r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f5,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((r1_xboole_0(X3,X7) | r1_xboole_0(X2,X6) | r1_xboole_0(X1,X5) | r1_xboole_0(X0,X4)) & ~r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (~r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) => (~r1_xboole_0(X3,X7) & ~r1_xboole_0(X2,X6) & ~r1_xboole_0(X1,X5) & ~r1_xboole_0(X0,X4)))),
% 0.22/0.43    inference(negated_conjecture,[],[f3])).
% 0.22/0.43  fof(f3,conjecture,(
% 0.22/0.43    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (~r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) => (~r1_xboole_0(X3,X7) & ~r1_xboole_0(X2,X6) & ~r1_xboole_0(X1,X5) & ~r1_xboole_0(X0,X4)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_mcart_1)).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    spl8_1 | spl8_2 | spl8_3 | spl8_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f10,f28,f24,f20,f16])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    r1_xboole_0(sK3,sK7) | r1_xboole_0(sK2,sK6) | r1_xboole_0(sK1,sK5) | r1_xboole_0(sK0,sK4)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (16981)------------------------------
% 0.22/0.43  % (16981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (16981)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (16981)Memory used [KB]: 6140
% 0.22/0.43  % (16981)Time elapsed: 0.003 s
% 0.22/0.43  % (16981)------------------------------
% 0.22/0.43  % (16981)------------------------------
% 0.22/0.43  % (16974)Success in time 0.066 s
%------------------------------------------------------------------------------
