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
% DateTime   : Thu Dec  3 12:45:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  64 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  114 ( 154 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f110,f136,f159,f221])).

fof(f221,plain,
    ( spl7_1
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f220,f104,f44])).

fof(f44,plain,
    ( spl7_1
  <=> r1_tarski(k1_setfam_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f104,plain,
    ( spl7_5
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k1_setfam_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f220,plain,
    ( r1_tarski(k1_setfam_1(sK1),sK0)
    | ~ spl7_5 ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( r1_tarski(k1_setfam_1(sK1),sK0)
    | r1_tarski(k1_setfam_1(sK1),sK0)
    | ~ spl7_5 ),
    inference(resolution,[],[f183,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f183,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(k1_setfam_1(sK1),X1),sK0)
        | r1_tarski(k1_setfam_1(sK1),X1) )
    | ~ spl7_5 ),
    inference(resolution,[],[f105,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_setfam_1(sK1))
        | r2_hidden(X0,sK0) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f159,plain,(
    ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl7_9 ),
    inference(resolution,[],[f143,f128])).

fof(f128,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_9
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f143,plain,
    ( ! [X0] : ~ r2_hidden(sK0,X0)
    | ~ spl7_9 ),
    inference(resolution,[],[f128,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f41,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f14,f15])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f14,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f136,plain,
    ( spl7_9
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f115,f107,f49,f126])).

fof(f49,plain,
    ( spl7_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f107,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f115,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f51,f109])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f51,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f110,plain,
    ( spl7_5
    | spl7_6
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f98,f49,f107,f104])).

fof(f98,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK1
        | r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k1_setfam_1(sK1)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f39,f51])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f52,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f12,f49])).

fof(f12,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),X0)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f47,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f13,f44])).

fof(f13,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:25:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (31849)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.46  % (31854)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.47  % (31857)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.47  % (31846)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.49  % (31857)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f47,f52,f110,f136,f159,f221])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    spl7_1 | ~spl7_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f220,f104,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    spl7_1 <=> r1_tarski(k1_setfam_1(sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl7_5 <=> ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,k1_setfam_1(sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    r1_tarski(k1_setfam_1(sK1),sK0) | ~spl7_5),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f215])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    r1_tarski(k1_setfam_1(sK1),sK0) | r1_tarski(k1_setfam_1(sK1),sK0) | ~spl7_5),
% 0.21/0.49    inference(resolution,[],[f183,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    ( ! [X1] : (r2_hidden(sK5(k1_setfam_1(sK1),X1),sK0) | r1_tarski(k1_setfam_1(sK1),X1)) ) | ~spl7_5),
% 0.21/0.49    inference(resolution,[],[f105,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_setfam_1(sK1)) | r2_hidden(X0,sK0)) ) | ~spl7_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f104])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ~spl7_9),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    $false | ~spl7_9),
% 0.21/0.49    inference(resolution,[],[f143,f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_xboole_0) | ~spl7_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f126])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl7_9 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK0,X0)) ) | ~spl7_9),
% 0.21/0.49    inference(resolution,[],[f128,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.49    inference(superposition,[],[f41,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(resolution,[],[f14,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    spl7_9 | ~spl7_2 | ~spl7_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f115,f107,f49,f126])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl7_2 <=> r2_hidden(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl7_6 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_xboole_0) | (~spl7_2 | ~spl7_6)),
% 0.21/0.49    inference(backward_demodulation,[],[f51,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl7_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    r2_hidden(sK0,sK1) | ~spl7_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl7_5 | spl7_6 | ~spl7_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f98,f49,f107,f104])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = sK1 | r2_hidden(X0,sK0) | ~r2_hidden(X0,k1_setfam_1(sK1))) ) | ~spl7_2),
% 0.21/0.49    inference(resolution,[],[f39,f51])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | k1_xboole_0 = X0 | r2_hidden(X2,X3) | ~r2_hidden(X2,k1_setfam_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl7_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f12,f49])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    r2_hidden(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),X0) & r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ~spl7_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f13,f44])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK1),sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (31857)------------------------------
% 0.21/0.49  % (31857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31857)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (31857)Memory used [KB]: 10746
% 0.21/0.49  % (31857)Time elapsed: 0.070 s
% 0.21/0.49  % (31857)------------------------------
% 0.21/0.49  % (31857)------------------------------
% 0.21/0.49  % (31840)Success in time 0.129 s
%------------------------------------------------------------------------------
