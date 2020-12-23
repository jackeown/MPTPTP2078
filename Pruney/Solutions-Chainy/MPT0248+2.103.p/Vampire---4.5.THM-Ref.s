%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:04 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 432 expanded)
%              Number of leaves         :   20 ( 138 expanded)
%              Depth                    :   14
%              Number of atoms          :  279 ( 915 expanded)
%              Number of equality atoms :   86 ( 611 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f766,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f166,f202,f306,f648,f701,f730,f765])).

fof(f765,plain,
    ( ~ spl4_3
    | ~ spl4_6
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f760])).

fof(f760,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_6
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f201,f731])).

fof(f731,plain,
    ( sK1 = sK2
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f668,f164])).

fof(f164,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl4_6
  <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f668,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f65,f664])).

fof(f664,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f107,f52])).

% (10919)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f52,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f107,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f65,plain,(
    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f35,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

% (10922)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f201,plain,
    ( sK1 != sK2
    | spl4_7 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl4_7
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f730,plain,
    ( spl4_2
    | ~ spl4_3
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f724])).

fof(f724,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f107,f722])).

fof(f722,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_2
    | ~ spl4_3
    | spl4_6 ),
    inference(forward_demodulation,[],[f719,f668])).

fof(f719,plain,
    ( ~ r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl4_2
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f98,f165,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f64,f64])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

% (10927)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f165,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f163])).

fof(f98,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f701,plain,
    ( spl4_1
    | ~ spl4_3
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f693])).

fof(f693,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f82,f680])).

fof(f680,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl4_1
    | ~ spl4_3
    | spl4_5 ),
    inference(backward_demodulation,[],[f171,f664])).

fof(f171,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | spl4_1
    | spl4_5 ),
    inference(forward_demodulation,[],[f168,f65])).

fof(f168,plain,
    ( ~ r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl4_1
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f94,f161,f71])).

fof(f161,plain,
    ( k1_xboole_0 != sK2
    | spl4_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f94,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_1
  <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

% (10908)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f648,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f640])).

fof(f640,plain,
    ( $false
    | ~ spl4_5
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f82,f612])).

fof(f612,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_5
    | spl4_6 ),
    inference(duplicate_literal_removal,[],[f611])).

fof(f611,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_5
    | spl4_6 ),
    inference(forward_demodulation,[],[f610,f506])).

fof(f506,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_5
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f341,f53,f349])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_xboole_0(sK1,k1_xboole_0))
        | k2_xboole_0(sK1,k1_xboole_0) = X0
        | k1_xboole_0 = X0 )
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f308,f160])).

fof(f160,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f308,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_xboole_0(sK1,k1_xboole_0))
        | k2_xboole_0(sK1,sK2) = X0
        | k1_xboole_0 = X0 )
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f84,f160])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
      | k2_xboole_0(sK1,sK2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f71,f65])).

% (10911)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f341,plain,
    ( sK1 != k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_5
    | spl4_6 ),
    inference(backward_demodulation,[],[f238,f160])).

fof(f238,plain,
    ( sK1 != k2_xboole_0(sK1,sK2)
    | spl4_6 ),
    inference(superposition,[],[f165,f65])).

fof(f610,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_5
    | spl4_6 ),
    inference(forward_demodulation,[],[f391,f506])).

fof(f391,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_5
    | spl4_6 ),
    inference(superposition,[],[f344,f52])).

fof(f344,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k1_xboole_0),sK1)
    | ~ spl4_5
    | spl4_6 ),
    inference(backward_demodulation,[],[f243,f160])).

fof(f243,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),sK1)
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f53,f238,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f306,plain,
    ( spl4_3
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | spl4_3
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f115,f117,f278,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f278,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),sK2)
    | spl4_5 ),
    inference(forward_demodulation,[],[f276,f65])).

fof(f276,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2)
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f270,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f45,f64])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f270,plain,
    ( r2_hidden(sK0,sK2)
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f190,f87])).

fof(f87,plain,(
    ! [X3] :
      ( r2_hidden(sK0,X3)
      | r1_xboole_0(k2_xboole_0(sK1,sK2),X3) ) ),
    inference(superposition,[],[f76,f65])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f190,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_xboole_0(X0,sK2),sK2)
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f174,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f174,plain,
    ( ! [X0] : ~ r1_xboole_0(sK2,k2_xboole_0(X0,sK2))
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f167,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f167,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f161,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f117,plain,
    ( ! [X0] : r2_hidden(sK3(sK1,sK2),k2_xboole_0(sK1,X0))
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f53,f114,f58])).

fof(f114,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f108,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f108,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f115,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK2)
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f108,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f202,plain,
    ( ~ spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f83,f163,f199])).

fof(f83,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f66])).

fof(f66,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f34,f64,f64])).

fof(f34,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f166,plain,
    ( ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f68,f163,f159])).

fof(f68,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f32,f64])).

fof(f32,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f99,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f67,f96,f92])).

fof(f67,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f33,f64])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (10902)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (10915)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (10923)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (10900)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (10901)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (10930)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (10920)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (10912)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (10904)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (10912)Refutation not found, incomplete strategy% (10912)------------------------------
% 0.20/0.52  % (10912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10912)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10912)Memory used [KB]: 10746
% 0.20/0.52  % (10912)Time elapsed: 0.127 s
% 0.20/0.52  % (10912)------------------------------
% 0.20/0.52  % (10912)------------------------------
% 1.30/0.53  % (10907)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.30/0.53  % (10910)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.30/0.53  % (10899)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.53  % (10906)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.30/0.53  % (10904)Refutation found. Thanks to Tanya!
% 1.30/0.53  % SZS status Theorem for theBenchmark
% 1.30/0.53  % (10905)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.53  % (10921)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.30/0.54  % (10928)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.54  % (10924)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.30/0.54  % (10929)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.30/0.54  % (10926)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.54  % (10932)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.46/0.54  % (10917)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.46/0.55  % (10916)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.46/0.55  % (10918)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.55  % SZS output start Proof for theBenchmark
% 1.46/0.55  fof(f766,plain,(
% 1.46/0.55    $false),
% 1.46/0.55    inference(avatar_sat_refutation,[],[f99,f166,f202,f306,f648,f701,f730,f765])).
% 1.46/0.55  fof(f765,plain,(
% 1.46/0.55    ~spl4_3 | ~spl4_6 | spl4_7),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f760])).
% 1.46/0.55  fof(f760,plain,(
% 1.46/0.55    $false | (~spl4_3 | ~spl4_6 | spl4_7)),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f201,f731])).
% 1.46/0.55  fof(f731,plain,(
% 1.46/0.55    sK1 = sK2 | (~spl4_3 | ~spl4_6)),
% 1.46/0.55    inference(backward_demodulation,[],[f668,f164])).
% 1.46/0.55  fof(f164,plain,(
% 1.46/0.55    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl4_6),
% 1.46/0.55    inference(avatar_component_clause,[],[f163])).
% 1.46/0.55  fof(f163,plain,(
% 1.46/0.55    spl4_6 <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.46/0.55  fof(f668,plain,(
% 1.46/0.55    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl4_3),
% 1.46/0.55    inference(backward_demodulation,[],[f65,f664])).
% 1.46/0.55  fof(f664,plain,(
% 1.46/0.55    sK2 = k2_xboole_0(sK1,sK2) | ~spl4_3),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f107,f52])).
% 1.46/0.55  % (10919)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.46/0.55  fof(f52,plain,(
% 1.46/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f29])).
% 1.46/0.55  fof(f29,plain,(
% 1.46/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.46/0.55    inference(ennf_transformation,[],[f7])).
% 1.46/0.55  fof(f7,axiom,(
% 1.46/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.46/0.55  fof(f107,plain,(
% 1.46/0.55    r1_tarski(sK1,sK2) | ~spl4_3),
% 1.46/0.55    inference(avatar_component_clause,[],[f106])).
% 1.46/0.55  fof(f106,plain,(
% 1.46/0.55    spl4_3 <=> r1_tarski(sK1,sK2)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.46/0.55  fof(f65,plain,(
% 1.46/0.55    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.46/0.55    inference(definition_unfolding,[],[f35,f64])).
% 1.46/0.55  fof(f64,plain,(
% 1.46/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.46/0.55    inference(definition_unfolding,[],[f48,f63])).
% 1.46/0.55  fof(f63,plain,(
% 1.46/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.46/0.55    inference(definition_unfolding,[],[f61,f62])).
% 1.46/0.55  fof(f62,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f13])).
% 1.46/0.55  fof(f13,axiom,(
% 1.46/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.46/0.55  % (10922)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.46/0.55  fof(f61,plain,(
% 1.46/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f12])).
% 1.46/0.55  fof(f12,axiom,(
% 1.46/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.46/0.55  fof(f48,plain,(
% 1.46/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f11])).
% 1.46/0.55  fof(f11,axiom,(
% 1.46/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.46/0.55  fof(f35,plain,(
% 1.46/0.55    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.46/0.55    inference(cnf_transformation,[],[f25])).
% 1.46/0.55  fof(f25,plain,(
% 1.46/0.55    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.46/0.55    inference(ennf_transformation,[],[f24])).
% 1.46/0.55  fof(f24,negated_conjecture,(
% 1.46/0.55    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.46/0.55    inference(negated_conjecture,[],[f23])).
% 1.46/0.55  fof(f23,conjecture,(
% 1.46/0.55    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.46/0.55  fof(f201,plain,(
% 1.46/0.55    sK1 != sK2 | spl4_7),
% 1.46/0.55    inference(avatar_component_clause,[],[f199])).
% 1.46/0.55  fof(f199,plain,(
% 1.46/0.55    spl4_7 <=> sK1 = sK2),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.46/0.55  fof(f730,plain,(
% 1.46/0.55    spl4_2 | ~spl4_3 | spl4_6),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f724])).
% 1.46/0.55  fof(f724,plain,(
% 1.46/0.55    $false | (spl4_2 | ~spl4_3 | spl4_6)),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f107,f722])).
% 1.46/0.55  fof(f722,plain,(
% 1.46/0.55    ~r1_tarski(sK1,sK2) | (spl4_2 | ~spl4_3 | spl4_6)),
% 1.46/0.55    inference(forward_demodulation,[],[f719,f668])).
% 1.46/0.55  fof(f719,plain,(
% 1.46/0.55    ~r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | (spl4_2 | spl4_6)),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f98,f165,f71])).
% 1.46/0.55  fof(f71,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.46/0.55    inference(definition_unfolding,[],[f38,f64,f64])).
% 1.46/0.55  fof(f38,plain,(
% 1.46/0.55    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.46/0.55    inference(cnf_transformation,[],[f20])).
% 1.46/0.55  % (10927)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.46/0.55  fof(f20,axiom,(
% 1.46/0.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.46/0.55  fof(f165,plain,(
% 1.46/0.55    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | spl4_6),
% 1.46/0.55    inference(avatar_component_clause,[],[f163])).
% 1.46/0.55  fof(f98,plain,(
% 1.46/0.55    k1_xboole_0 != sK1 | spl4_2),
% 1.46/0.55    inference(avatar_component_clause,[],[f96])).
% 1.46/0.55  fof(f96,plain,(
% 1.46/0.55    spl4_2 <=> k1_xboole_0 = sK1),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.46/0.55  fof(f701,plain,(
% 1.46/0.55    spl4_1 | ~spl4_3 | spl4_5),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f693])).
% 1.46/0.55  fof(f693,plain,(
% 1.46/0.55    $false | (spl4_1 | ~spl4_3 | spl4_5)),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f82,f680])).
% 1.46/0.55  fof(f680,plain,(
% 1.46/0.55    ~r1_tarski(sK2,sK2) | (spl4_1 | ~spl4_3 | spl4_5)),
% 1.46/0.55    inference(backward_demodulation,[],[f171,f664])).
% 1.46/0.55  fof(f171,plain,(
% 1.46/0.55    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | (spl4_1 | spl4_5)),
% 1.46/0.55    inference(forward_demodulation,[],[f168,f65])).
% 1.46/0.55  fof(f168,plain,(
% 1.46/0.55    ~r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | (spl4_1 | spl4_5)),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f94,f161,f71])).
% 1.46/0.55  fof(f161,plain,(
% 1.46/0.55    k1_xboole_0 != sK2 | spl4_5),
% 1.46/0.55    inference(avatar_component_clause,[],[f159])).
% 1.46/0.55  fof(f159,plain,(
% 1.46/0.55    spl4_5 <=> k1_xboole_0 = sK2),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.46/0.55  fof(f94,plain,(
% 1.46/0.55    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | spl4_1),
% 1.46/0.55    inference(avatar_component_clause,[],[f92])).
% 1.46/0.55  fof(f92,plain,(
% 1.46/0.55    spl4_1 <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.46/0.55  fof(f82,plain,(
% 1.46/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.46/0.55    inference(equality_resolution,[],[f54])).
% 1.46/0.55  fof(f54,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.46/0.55    inference(cnf_transformation,[],[f4])).
% 1.46/0.55  % (10908)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.46/0.55  fof(f4,axiom,(
% 1.46/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.46/0.55  fof(f648,plain,(
% 1.46/0.55    ~spl4_5 | spl4_6),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f640])).
% 1.46/0.55  fof(f640,plain,(
% 1.46/0.55    $false | (~spl4_5 | spl4_6)),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f82,f612])).
% 1.46/0.55  fof(f612,plain,(
% 1.46/0.55    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl4_5 | spl4_6)),
% 1.46/0.55    inference(duplicate_literal_removal,[],[f611])).
% 1.46/0.55  fof(f611,plain,(
% 1.46/0.55    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl4_5 | spl4_6)),
% 1.46/0.55    inference(forward_demodulation,[],[f610,f506])).
% 1.46/0.55  fof(f506,plain,(
% 1.46/0.55    k1_xboole_0 = sK1 | (~spl4_5 | spl4_6)),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f341,f53,f349])).
% 1.46/0.55  fof(f349,plain,(
% 1.46/0.55    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,k1_xboole_0)) | k2_xboole_0(sK1,k1_xboole_0) = X0 | k1_xboole_0 = X0) ) | ~spl4_5),
% 1.46/0.55    inference(forward_demodulation,[],[f308,f160])).
% 1.46/0.55  fof(f160,plain,(
% 1.46/0.55    k1_xboole_0 = sK2 | ~spl4_5),
% 1.46/0.55    inference(avatar_component_clause,[],[f159])).
% 1.46/0.55  fof(f308,plain,(
% 1.46/0.55    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,k1_xboole_0)) | k2_xboole_0(sK1,sK2) = X0 | k1_xboole_0 = X0) ) | ~spl4_5),
% 1.46/0.55    inference(backward_demodulation,[],[f84,f160])).
% 1.46/0.55  fof(f84,plain,(
% 1.46/0.55    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = X0 | k1_xboole_0 = X0) )),
% 1.46/0.55    inference(superposition,[],[f71,f65])).
% 1.46/0.55  % (10911)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.46/0.55  fof(f53,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.46/0.55    inference(cnf_transformation,[],[f10])).
% 1.46/0.55  fof(f10,axiom,(
% 1.46/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.46/0.55  fof(f341,plain,(
% 1.46/0.55    sK1 != k2_xboole_0(sK1,k1_xboole_0) | (~spl4_5 | spl4_6)),
% 1.46/0.55    inference(backward_demodulation,[],[f238,f160])).
% 1.46/0.55  fof(f238,plain,(
% 1.46/0.55    sK1 != k2_xboole_0(sK1,sK2) | spl4_6),
% 1.46/0.55    inference(superposition,[],[f165,f65])).
% 1.46/0.55  fof(f610,plain,(
% 1.46/0.55    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r1_tarski(sK1,k1_xboole_0) | (~spl4_5 | spl4_6)),
% 1.46/0.55    inference(forward_demodulation,[],[f391,f506])).
% 1.46/0.55  fof(f391,plain,(
% 1.46/0.55    ~r1_tarski(k1_xboole_0,sK1) | ~r1_tarski(sK1,k1_xboole_0) | (~spl4_5 | spl4_6)),
% 1.46/0.55    inference(superposition,[],[f344,f52])).
% 1.46/0.55  fof(f344,plain,(
% 1.46/0.55    ~r1_tarski(k2_xboole_0(sK1,k1_xboole_0),sK1) | (~spl4_5 | spl4_6)),
% 1.46/0.55    inference(backward_demodulation,[],[f243,f160])).
% 1.46/0.55  fof(f243,plain,(
% 1.46/0.55    ~r1_tarski(k2_xboole_0(sK1,sK2),sK1) | spl4_6),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f53,f238,f56])).
% 1.46/0.55  fof(f56,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.46/0.55    inference(cnf_transformation,[],[f4])).
% 1.46/0.55  fof(f306,plain,(
% 1.46/0.55    spl4_3 | spl4_5),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f293])).
% 1.46/0.55  fof(f293,plain,(
% 1.46/0.55    $false | (spl4_3 | spl4_5)),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f115,f117,f278,f58])).
% 1.46/0.55  fof(f58,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f31])).
% 1.46/0.55  fof(f31,plain,(
% 1.46/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.46/0.55    inference(ennf_transformation,[],[f1])).
% 1.46/0.55  fof(f1,axiom,(
% 1.46/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.46/0.55  fof(f278,plain,(
% 1.46/0.55    r1_tarski(k2_xboole_0(sK1,sK2),sK2) | spl4_5),
% 1.46/0.55    inference(forward_demodulation,[],[f276,f65])).
% 1.46/0.55  fof(f276,plain,(
% 1.46/0.55    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2) | spl4_5),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f270,f75])).
% 1.46/0.55  fof(f75,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 1.46/0.55    inference(definition_unfolding,[],[f45,f64])).
% 1.46/0.55  fof(f45,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f18])).
% 1.46/0.55  fof(f18,axiom,(
% 1.46/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.46/0.55  fof(f270,plain,(
% 1.46/0.55    r2_hidden(sK0,sK2) | spl4_5),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f190,f87])).
% 1.46/0.55  fof(f87,plain,(
% 1.46/0.55    ( ! [X3] : (r2_hidden(sK0,X3) | r1_xboole_0(k2_xboole_0(sK1,sK2),X3)) )),
% 1.46/0.55    inference(superposition,[],[f76,f65])).
% 1.46/0.55  fof(f76,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.46/0.55    inference(definition_unfolding,[],[f47,f64])).
% 1.46/0.55  fof(f47,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f27])).
% 1.46/0.55  fof(f27,plain,(
% 1.46/0.55    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.46/0.55    inference(ennf_transformation,[],[f19])).
% 1.46/0.55  fof(f19,axiom,(
% 1.46/0.55    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.46/0.55  fof(f190,plain,(
% 1.46/0.55    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(X0,sK2),sK2)) ) | spl4_5),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f174,f57])).
% 1.46/0.55  fof(f57,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f30])).
% 1.46/0.55  fof(f30,plain,(
% 1.46/0.55    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.46/0.55    inference(ennf_transformation,[],[f3])).
% 1.46/0.55  fof(f3,axiom,(
% 1.46/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.46/0.55  fof(f174,plain,(
% 1.46/0.55    ( ! [X0] : (~r1_xboole_0(sK2,k2_xboole_0(X0,sK2))) ) | spl4_5),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f167,f50])).
% 1.46/0.55  fof(f50,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.46/0.55    inference(cnf_transformation,[],[f28])).
% 1.46/0.55  fof(f28,plain,(
% 1.46/0.55    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.46/0.55    inference(ennf_transformation,[],[f9])).
% 1.46/0.55  fof(f9,axiom,(
% 1.46/0.55    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.46/0.55  fof(f167,plain,(
% 1.46/0.55    ~r1_xboole_0(sK2,sK2) | spl4_5),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f161,f41])).
% 1.46/0.55  fof(f41,plain,(
% 1.46/0.55    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.46/0.55    inference(cnf_transformation,[],[f26])).
% 1.46/0.55  fof(f26,plain,(
% 1.46/0.55    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.46/0.55    inference(ennf_transformation,[],[f8])).
% 1.46/0.55  fof(f8,axiom,(
% 1.46/0.55    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.46/0.55  fof(f117,plain,(
% 1.46/0.55    ( ! [X0] : (r2_hidden(sK3(sK1,sK2),k2_xboole_0(sK1,X0))) ) | spl4_3),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f53,f114,f58])).
% 1.46/0.55  fof(f114,plain,(
% 1.46/0.55    r2_hidden(sK3(sK1,sK2),sK1) | spl4_3),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f108,f59])).
% 1.46/0.55  fof(f59,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f31])).
% 1.46/0.55  fof(f108,plain,(
% 1.46/0.55    ~r1_tarski(sK1,sK2) | spl4_3),
% 1.46/0.55    inference(avatar_component_clause,[],[f106])).
% 1.46/0.55  fof(f115,plain,(
% 1.46/0.55    ~r2_hidden(sK3(sK1,sK2),sK2) | spl4_3),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f108,f60])).
% 1.46/0.55  fof(f60,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f31])).
% 1.46/0.55  fof(f202,plain,(
% 1.46/0.55    ~spl4_7 | ~spl4_6),
% 1.46/0.55    inference(avatar_split_clause,[],[f83,f163,f199])).
% 1.46/0.55  fof(f83,plain,(
% 1.46/0.55    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != sK2),
% 1.46/0.55    inference(inner_rewriting,[],[f66])).
% 1.46/0.55  fof(f66,plain,(
% 1.46/0.55    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.46/0.55    inference(definition_unfolding,[],[f34,f64,f64])).
% 1.46/0.55  fof(f34,plain,(
% 1.46/0.55    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.46/0.55    inference(cnf_transformation,[],[f25])).
% 1.46/0.55  fof(f166,plain,(
% 1.46/0.55    ~spl4_5 | ~spl4_6),
% 1.46/0.55    inference(avatar_split_clause,[],[f68,f163,f159])).
% 1.46/0.55  fof(f68,plain,(
% 1.46/0.55    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.46/0.55    inference(definition_unfolding,[],[f32,f64])).
% 1.46/0.55  fof(f32,plain,(
% 1.46/0.55    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.46/0.55    inference(cnf_transformation,[],[f25])).
% 1.46/0.55  fof(f99,plain,(
% 1.46/0.55    ~spl4_1 | ~spl4_2),
% 1.46/0.55    inference(avatar_split_clause,[],[f67,f96,f92])).
% 1.46/0.55  fof(f67,plain,(
% 1.46/0.55    k1_xboole_0 != sK1 | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.46/0.55    inference(definition_unfolding,[],[f33,f64])).
% 1.46/0.55  fof(f33,plain,(
% 1.46/0.55    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.46/0.55    inference(cnf_transformation,[],[f25])).
% 1.46/0.55  % SZS output end Proof for theBenchmark
% 1.46/0.55  % (10904)------------------------------
% 1.46/0.55  % (10904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (10904)Termination reason: Refutation
% 1.46/0.55  
% 1.46/0.55  % (10904)Memory used [KB]: 6524
% 1.46/0.55  % (10904)Time elapsed: 0.116 s
% 1.46/0.55  % (10904)------------------------------
% 1.46/0.55  % (10904)------------------------------
% 1.46/0.55  % (10914)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.46/0.55  % (10913)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.46/0.55  % (10911)Refutation not found, incomplete strategy% (10911)------------------------------
% 1.46/0.55  % (10911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (10911)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (10911)Memory used [KB]: 10618
% 1.46/0.55  % (10911)Time elapsed: 0.152 s
% 1.46/0.55  % (10911)------------------------------
% 1.46/0.55  % (10911)------------------------------
% 1.46/0.56  % (10893)Success in time 0.195 s
%------------------------------------------------------------------------------
