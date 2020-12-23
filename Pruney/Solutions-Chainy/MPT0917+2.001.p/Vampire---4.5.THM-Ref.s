%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  81 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 233 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f42,f60,f63,f69])).

fof(f69,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl6_4 ),
    inference(resolution,[],[f59,f13])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5))
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5))
      & r1_tarski(sK4,sK5)
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X4,X5)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_mcart_1)).

fof(f59,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl6_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f63,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | spl6_3 ),
    inference(resolution,[],[f55,f14])).

fof(f14,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f55,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl6_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f60,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_2 ),
    inference(avatar_split_clause,[],[f50,f33,f57,f53])).

fof(f33,plain,
    ( spl6_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f50,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_tarski(sK2,sK3)
    | spl6_2 ),
    inference(resolution,[],[f44,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f44,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(sK1,sK3))
        | ~ r1_tarski(sK0,X0) )
    | spl6_2 ),
    inference(resolution,[],[f43,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),X0)
        | ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK3)) )
    | spl6_2 ),
    inference(resolution,[],[f35,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f35,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f42,plain,
    ( ~ spl6_2
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f40,f29,f33])).

fof(f29,plain,
    ( spl6_1
  <=> r1_tarski(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f40,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(resolution,[],[f24,f18])).

fof(f24,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),X1),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5))
      | ~ r1_tarski(sK4,X1) ) ),
    inference(resolution,[],[f22,f19])).

fof(f22,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5)) ) ),
    inference(resolution,[],[f20,f21])).

fof(f21,plain,(
    ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5)) ),
    inference(definition_unfolding,[],[f16,f17,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f16,plain,(
    ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f37])).

fof(f37,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f31,f15])).

fof(f15,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,
    ( ~ r1_tarski(sK4,sK5)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (2002)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (1996)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (1996)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f39,f42,f60,f63,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl6_4),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    $false | spl6_4),
% 0.20/0.47    inference(resolution,[],[f59,f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ~r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5)) & r1_tarski(sK4,sK5) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) & r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5)) & r1_tarski(sK4,sK5) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) & r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f6])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) & (r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)))),
% 0.20/0.47    inference(negated_conjecture,[],[f4])).
% 0.20/0.47  fof(f4,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_mcart_1)).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK1) | spl6_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl6_4 <=> r1_tarski(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    spl6_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    $false | spl6_3),
% 0.20/0.47    inference(resolution,[],[f55,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    r1_tarski(sK2,sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ~r1_tarski(sK2,sK3) | spl6_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl6_3 <=> r1_tarski(sK2,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ~spl6_3 | ~spl6_4 | spl6_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f50,f33,f57,f53])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    spl6_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK1) | ~r1_tarski(sK2,sK3) | spl6_2),
% 0.20/0.47    inference(resolution,[],[f44,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(sK1,sK3)) | ~r1_tarski(sK0,X0)) ) | spl6_2),
% 0.20/0.47    inference(resolution,[],[f43,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK2),X0) | ~r1_tarski(X0,k2_zfmisc_1(sK1,sK3))) ) | spl6_2),
% 0.20/0.47    inference(resolution,[],[f35,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) | spl6_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f33])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ~spl6_2 | ~spl6_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f40,f29,f33])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    spl6_1 <=> r1_tarski(sK4,sK5)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ~r1_tarski(sK4,sK5) | ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.20/0.47    inference(resolution,[],[f24,f18])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),X1),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5)) | ~r1_tarski(sK4,X1)) )),
% 0.20/0.47    inference(resolution,[],[f22,f19])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),X0) | ~r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5))) )),
% 0.20/0.47    inference(resolution,[],[f20,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5))),
% 0.20/0.47    inference(definition_unfolding,[],[f16,f17,f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ~r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5))),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    spl6_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    $false | spl6_1),
% 0.20/0.47    inference(resolution,[],[f31,f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    r1_tarski(sK4,sK5)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ~r1_tarski(sK4,sK5) | spl6_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f29])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (1996)------------------------------
% 0.20/0.47  % (1996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (1996)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (1996)Memory used [KB]: 6140
% 0.20/0.47  % (1996)Time elapsed: 0.052 s
% 0.20/0.47  % (1996)------------------------------
% 0.20/0.47  % (1996)------------------------------
% 0.20/0.47  % (1990)Success in time 0.111 s
%------------------------------------------------------------------------------
