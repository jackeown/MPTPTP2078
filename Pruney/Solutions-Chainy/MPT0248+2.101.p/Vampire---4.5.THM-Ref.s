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
% DateTime   : Thu Dec  3 12:38:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 327 expanded)
%              Number of leaves         :   16 (  92 expanded)
%              Depth                    :   12
%              Number of atoms          :  232 ( 928 expanded)
%              Number of equality atoms :   93 ( 615 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1331,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f143,f214,f1040,f1140,f1230,f1330])).

fof(f1330,plain,
    ( spl7_2
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f1326])).

fof(f1326,plain,
    ( $false
    | spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f92,f773])).

fof(f773,plain,
    ( k1_xboole_0 = sK1
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f239,f39,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
      | k2_xboole_0(sK1,sK2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f62,f56])).

fof(f56,plain,(
    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f27,f40])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X1))
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f40,f40])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f239,plain,
    ( sK1 != k2_xboole_0(sK1,sK2)
    | spl7_4 ),
    inference(superposition,[],[f142,f56])).

% (27594)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f142,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl7_4
  <=> sK1 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f92,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1230,plain,
    ( ~ spl7_1
    | ~ spl7_4
    | spl7_5 ),
    inference(avatar_contradiction_clause,[],[f1225])).

fof(f1225,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_4
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f213,f1143])).

fof(f1143,plain,
    ( sK1 = sK2
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f87,f141])).

fof(f141,plain,
    ( sK1 = k2_tarski(sK0,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f87,plain,
    ( sK2 = k2_tarski(sK0,sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl7_1
  <=> sK2 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f213,plain,
    ( sK1 != sK2
    | spl7_5 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl7_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f1140,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_contradiction_clause,[],[f1132])).

% (27596)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (27587)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (27597)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (27586)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (27595)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f1132,plain,
    ( $false
    | spl7_1
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f69,f760,f543,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f543,plain,
    ( r2_hidden(sK0,sK2)
    | spl7_3 ),
    inference(backward_demodulation,[],[f144,f531])).

fof(f531,plain,
    ( sK0 = sK3(sK2)
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f167,f84])).

fof(f84,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_xboole_0(sK1,sK2))
      | sK0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_xboole_0(sK1,sK2))
      | sK0 = X1
      | sK0 = X1 ) ),
    inference(superposition,[],[f74,f56])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f167,plain,
    ( ! [X0] : r2_hidden(sK3(sK2),k2_xboole_0(X0,sK2))
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f144,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f144,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f138,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f138,plain,
    ( k1_xboole_0 != sK2
    | spl7_3 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f760,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl7_1 ),
    inference(backward_demodulation,[],[f133,f750])).

fof(f750,plain,
    ( sK0 = sK5(sK1,sK2)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f132,f532])).

fof(f532,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK0 = X0 ) ),
    inference(resolution,[],[f84,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f132,plain,
    ( r2_hidden(sK5(sK1,sK2),sK1)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f123,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f123,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f102,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f102,plain,
    ( sK2 != k2_xboole_0(sK1,sK2)
    | spl7_1 ),
    inference(superposition,[],[f88,f56])).

fof(f88,plain,
    ( sK2 != k2_tarski(sK0,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f133,plain,
    ( ~ r2_hidden(sK5(sK1,sK2),sK2)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f123,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1040,plain,
    ( spl7_1
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f1028])).

fof(f1028,plain,
    ( $false
    | spl7_1
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f760,f512,f760,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f512,plain,
    ( ! [X0] : r2_hidden(sK0,k2_xboole_0(X0,sK2))
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f497,f65])).

fof(f497,plain,
    ( r2_hidden(sK0,sK2)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f80,f479,f67])).

fof(f479,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f262,f83])).

fof(f83,plain,(
    ! [X2] :
      ( r1_tarski(k2_xboole_0(sK1,sK2),X2)
      | ~ r2_hidden(sK0,X2) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X2] :
      ( r1_tarski(k2_xboole_0(sK1,sK2),X2)
      | ~ r2_hidden(sK0,X2)
      | ~ r2_hidden(sK0,X2) ) ),
    inference(superposition,[],[f43,f56])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f262,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),sK1)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f39,f239,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f80,plain,(
    r2_hidden(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f73,f56])).

fof(f73,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_tarski(X3,X1)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f214,plain,
    ( ~ spl7_5
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f75,f140,f211])).

fof(f75,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f57])).

fof(f57,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | sK2 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f26,f40,f40])).

fof(f26,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f143,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f59,f140,f136])).

fof(f59,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f24,f40])).

fof(f24,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f93,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f58,f90,f86])).

fof(f58,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f25,f40])).

fof(f25,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:25:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (27580)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (27593)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.49  % (27585)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (27589)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (27577)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (27578)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (27601)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.50  % (27581)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (27604)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (27605)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (27579)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (27588)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (27602)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (27582)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (27592)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (27591)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (27599)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (27598)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (27603)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (27576)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (27584)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (27583)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (27580)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f1331,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f93,f143,f214,f1040,f1140,f1230,f1330])).
% 0.21/0.53  fof(f1330,plain,(
% 0.21/0.53    spl7_2 | spl7_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1326])).
% 0.21/0.53  fof(f1326,plain,(
% 0.21/0.53    $false | (spl7_2 | spl7_4)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f92,f773])).
% 0.21/0.53  fof(f773,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | spl7_4),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f239,f39,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(superposition,[],[f62,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0)),
% 0.21/0.53    inference(definition_unfolding,[],[f27,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.54    inference(negated_conjecture,[],[f18])).
% 0.21/0.54  fof(f18,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X1)) | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f28,f40,f40])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.54  fof(f239,plain,(
% 0.21/0.54    sK1 != k2_xboole_0(sK1,sK2) | spl7_4),
% 0.21/0.54    inference(superposition,[],[f142,f56])).
% 0.21/0.54  % (27594)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    sK1 != k2_tarski(sK0,sK0) | spl7_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f140])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    spl7_4 <=> sK1 = k2_tarski(sK0,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | spl7_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f90])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    spl7_2 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.54  fof(f1230,plain,(
% 0.21/0.54    ~spl7_1 | ~spl7_4 | spl7_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1225])).
% 0.21/0.54  fof(f1225,plain,(
% 0.21/0.54    $false | (~spl7_1 | ~spl7_4 | spl7_5)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f213,f1143])).
% 0.21/0.54  fof(f1143,plain,(
% 0.21/0.54    sK1 = sK2 | (~spl7_1 | ~spl7_4)),
% 0.21/0.54    inference(forward_demodulation,[],[f87,f141])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    sK1 = k2_tarski(sK0,sK0) | ~spl7_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f140])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    sK2 = k2_tarski(sK0,sK0) | ~spl7_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    spl7_1 <=> sK2 = k2_tarski(sK0,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.54  fof(f213,plain,(
% 0.21/0.54    sK1 != sK2 | spl7_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f211])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    spl7_5 <=> sK1 = sK2),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.54  fof(f1140,plain,(
% 0.21/0.54    spl7_1 | spl7_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1132])).
% 0.21/0.54  % (27596)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.54  % (27587)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.54  % (27597)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.54  % (27586)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.54  % (27595)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.54  fof(f1132,plain,(
% 1.43/0.54    $false | (spl7_1 | spl7_3)),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f69,f760,f543,f44])).
% 1.43/0.54  fof(f44,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f23])).
% 1.43/0.54  fof(f23,plain,(
% 1.43/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.43/0.54    inference(ennf_transformation,[],[f1])).
% 1.43/0.54  fof(f1,axiom,(
% 1.43/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.43/0.54  fof(f543,plain,(
% 1.43/0.54    r2_hidden(sK0,sK2) | spl7_3),
% 1.43/0.54    inference(backward_demodulation,[],[f144,f531])).
% 1.43/0.54  fof(f531,plain,(
% 1.43/0.54    sK0 = sK3(sK2) | spl7_3),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f167,f84])).
% 1.43/0.54  fof(f84,plain,(
% 1.43/0.54    ( ! [X1] : (~r2_hidden(X1,k2_xboole_0(sK1,sK2)) | sK0 = X1) )),
% 1.43/0.54    inference(duplicate_literal_removal,[],[f79])).
% 1.43/0.54  fof(f79,plain,(
% 1.43/0.54    ( ! [X1] : (~r2_hidden(X1,k2_xboole_0(sK1,sK2)) | sK0 = X1 | sK0 = X1) )),
% 1.43/0.54    inference(superposition,[],[f74,f56])).
% 1.43/0.54  fof(f74,plain,(
% 1.43/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.43/0.54    inference(equality_resolution,[],[f53])).
% 1.43/0.54  fof(f53,plain,(
% 1.43/0.54    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.43/0.54    inference(cnf_transformation,[],[f7])).
% 1.43/0.54  fof(f7,axiom,(
% 1.43/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.43/0.54  fof(f167,plain,(
% 1.43/0.54    ( ! [X0] : (r2_hidden(sK3(sK2),k2_xboole_0(X0,sK2))) ) | spl7_3),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f144,f65])).
% 1.43/0.54  fof(f65,plain,(
% 1.43/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.43/0.54    inference(equality_resolution,[],[f37])).
% 1.43/0.54  fof(f37,plain,(
% 1.43/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.43/0.54    inference(cnf_transformation,[],[f2])).
% 1.43/0.54  fof(f2,axiom,(
% 1.43/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.43/0.54  fof(f144,plain,(
% 1.43/0.54    r2_hidden(sK3(sK2),sK2) | spl7_3),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f138,f31])).
% 1.43/0.54  fof(f31,plain,(
% 1.43/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.43/0.54    inference(cnf_transformation,[],[f21])).
% 1.43/0.54  fof(f21,plain,(
% 1.43/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.43/0.54    inference(ennf_transformation,[],[f3])).
% 1.43/0.54  fof(f3,axiom,(
% 1.43/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.43/0.54  fof(f138,plain,(
% 1.43/0.54    k1_xboole_0 != sK2 | spl7_3),
% 1.43/0.54    inference(avatar_component_clause,[],[f136])).
% 1.43/0.54  fof(f136,plain,(
% 1.43/0.54    spl7_3 <=> k1_xboole_0 = sK2),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.43/0.54  fof(f760,plain,(
% 1.43/0.54    ~r2_hidden(sK0,sK2) | spl7_1),
% 1.43/0.54    inference(backward_demodulation,[],[f133,f750])).
% 1.43/0.54  fof(f750,plain,(
% 1.43/0.54    sK0 = sK5(sK1,sK2) | spl7_1),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f132,f532])).
% 1.43/0.54  fof(f532,plain,(
% 1.43/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | sK0 = X0) )),
% 1.43/0.54    inference(resolution,[],[f84,f66])).
% 1.43/0.54  fof(f66,plain,(
% 1.43/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 1.43/0.54    inference(equality_resolution,[],[f36])).
% 1.43/0.54  fof(f36,plain,(
% 1.43/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.43/0.54    inference(cnf_transformation,[],[f2])).
% 1.43/0.54  fof(f132,plain,(
% 1.43/0.54    r2_hidden(sK5(sK1,sK2),sK1) | spl7_1),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f123,f45])).
% 1.43/0.54  fof(f45,plain,(
% 1.43/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f23])).
% 1.43/0.54  fof(f123,plain,(
% 1.43/0.54    ~r1_tarski(sK1,sK2) | spl7_1),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f102,f38])).
% 1.43/0.54  fof(f38,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.43/0.54    inference(cnf_transformation,[],[f22])).
% 1.43/0.54  fof(f22,plain,(
% 1.43/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.43/0.54    inference(ennf_transformation,[],[f5])).
% 1.43/0.54  fof(f5,axiom,(
% 1.43/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.43/0.54  fof(f102,plain,(
% 1.43/0.54    sK2 != k2_xboole_0(sK1,sK2) | spl7_1),
% 1.43/0.54    inference(superposition,[],[f88,f56])).
% 1.43/0.54  fof(f88,plain,(
% 1.43/0.54    sK2 != k2_tarski(sK0,sK0) | spl7_1),
% 1.43/0.54    inference(avatar_component_clause,[],[f86])).
% 1.43/0.54  fof(f133,plain,(
% 1.43/0.54    ~r2_hidden(sK5(sK1,sK2),sK2) | spl7_1),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f123,f46])).
% 1.43/0.54  fof(f46,plain,(
% 1.43/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f23])).
% 1.43/0.54  fof(f69,plain,(
% 1.43/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.43/0.54    inference(equality_resolution,[],[f47])).
% 1.43/0.54  fof(f47,plain,(
% 1.43/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.43/0.54    inference(cnf_transformation,[],[f4])).
% 1.43/0.54  fof(f4,axiom,(
% 1.43/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.43/0.54  fof(f1040,plain,(
% 1.43/0.54    spl7_1 | spl7_4),
% 1.43/0.54    inference(avatar_contradiction_clause,[],[f1028])).
% 1.43/0.54  fof(f1028,plain,(
% 1.43/0.54    $false | (spl7_1 | spl7_4)),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f760,f512,f760,f67])).
% 1.43/0.54  fof(f67,plain,(
% 1.43/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 1.43/0.54    inference(equality_resolution,[],[f35])).
% 1.43/0.54  fof(f35,plain,(
% 1.43/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.43/0.54    inference(cnf_transformation,[],[f2])).
% 1.43/0.54  fof(f512,plain,(
% 1.43/0.54    ( ! [X0] : (r2_hidden(sK0,k2_xboole_0(X0,sK2))) ) | spl7_4),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f497,f65])).
% 1.43/0.54  fof(f497,plain,(
% 1.43/0.54    r2_hidden(sK0,sK2) | spl7_4),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f80,f479,f67])).
% 1.43/0.54  fof(f479,plain,(
% 1.43/0.54    ~r2_hidden(sK0,sK1) | spl7_4),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f262,f83])).
% 1.43/0.54  fof(f83,plain,(
% 1.43/0.54    ( ! [X2] : (r1_tarski(k2_xboole_0(sK1,sK2),X2) | ~r2_hidden(sK0,X2)) )),
% 1.43/0.54    inference(duplicate_literal_removal,[],[f82])).
% 1.43/0.54  fof(f82,plain,(
% 1.43/0.54    ( ! [X2] : (r1_tarski(k2_xboole_0(sK1,sK2),X2) | ~r2_hidden(sK0,X2) | ~r2_hidden(sK0,X2)) )),
% 1.43/0.54    inference(superposition,[],[f43,f56])).
% 1.43/0.54  fof(f43,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f17])).
% 1.43/0.54  fof(f17,axiom,(
% 1.43/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.43/0.54  fof(f262,plain,(
% 1.43/0.54    ~r1_tarski(k2_xboole_0(sK1,sK2),sK1) | spl7_4),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f39,f239,f49])).
% 1.43/0.54  fof(f49,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.43/0.54    inference(cnf_transformation,[],[f4])).
% 1.43/0.54  fof(f80,plain,(
% 1.43/0.54    r2_hidden(sK0,k2_xboole_0(sK1,sK2))),
% 1.43/0.54    inference(superposition,[],[f73,f56])).
% 1.43/0.54  fof(f73,plain,(
% 1.43/0.54    ( ! [X3,X1] : (r2_hidden(X3,k2_tarski(X3,X1))) )),
% 1.43/0.54    inference(equality_resolution,[],[f72])).
% 1.43/0.54  fof(f72,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_tarski(X3,X1) != X2) )),
% 1.43/0.54    inference(equality_resolution,[],[f54])).
% 1.43/0.54  fof(f54,plain,(
% 1.43/0.54    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.43/0.54    inference(cnf_transformation,[],[f7])).
% 1.43/0.54  fof(f214,plain,(
% 1.43/0.54    ~spl7_5 | ~spl7_4),
% 1.43/0.54    inference(avatar_split_clause,[],[f75,f140,f211])).
% 1.43/0.54  fof(f75,plain,(
% 1.43/0.54    sK1 != k2_tarski(sK0,sK0) | sK1 != sK2),
% 1.43/0.54    inference(inner_rewriting,[],[f57])).
% 1.43/0.54  fof(f57,plain,(
% 1.43/0.54    sK1 != k2_tarski(sK0,sK0) | sK2 != k2_tarski(sK0,sK0)),
% 1.43/0.54    inference(definition_unfolding,[],[f26,f40,f40])).
% 1.43/0.54  fof(f26,plain,(
% 1.43/0.54    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.43/0.54    inference(cnf_transformation,[],[f20])).
% 1.43/0.54  fof(f143,plain,(
% 1.43/0.54    ~spl7_3 | ~spl7_4),
% 1.43/0.54    inference(avatar_split_clause,[],[f59,f140,f136])).
% 1.43/0.54  fof(f59,plain,(
% 1.43/0.54    sK1 != k2_tarski(sK0,sK0) | k1_xboole_0 != sK2),
% 1.43/0.54    inference(definition_unfolding,[],[f24,f40])).
% 1.43/0.54  fof(f24,plain,(
% 1.43/0.54    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.43/0.54    inference(cnf_transformation,[],[f20])).
% 1.43/0.54  fof(f93,plain,(
% 1.43/0.54    ~spl7_1 | ~spl7_2),
% 1.43/0.54    inference(avatar_split_clause,[],[f58,f90,f86])).
% 1.43/0.54  fof(f58,plain,(
% 1.43/0.54    k1_xboole_0 != sK1 | sK2 != k2_tarski(sK0,sK0)),
% 1.43/0.54    inference(definition_unfolding,[],[f25,f40])).
% 1.43/0.54  fof(f25,plain,(
% 1.43/0.54    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.43/0.54    inference(cnf_transformation,[],[f20])).
% 1.43/0.54  % SZS output end Proof for theBenchmark
% 1.43/0.54  % (27580)------------------------------
% 1.43/0.54  % (27580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (27580)Termination reason: Refutation
% 1.43/0.54  
% 1.43/0.54  % (27580)Memory used [KB]: 6652
% 1.43/0.54  % (27580)Time elapsed: 0.147 s
% 1.43/0.54  % (27580)------------------------------
% 1.43/0.54  % (27580)------------------------------
% 1.43/0.54  % (27590)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.55  % (27575)Success in time 0.192 s
%------------------------------------------------------------------------------
