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
% DateTime   : Thu Dec  3 12:51:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 385 expanded)
%              Number of leaves         :   17 ( 101 expanded)
%              Depth                    :   14
%              Number of atoms          :  253 ( 900 expanded)
%              Number of equality atoms :  110 ( 492 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f453,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f174,f186,f190,f206,f320,f452])).

fof(f452,plain,
    ( ~ spl8_5
    | spl8_6 ),
    inference(avatar_contradiction_clause,[],[f444])).

fof(f444,plain,
    ( $false
    | ~ spl8_5
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f204,f424])).

% (30560)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f424,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f157,f423])).

fof(f423,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl8_5 ),
    inference(superposition,[],[f84,f362])).

fof(f362,plain,
    ( sK1 = k7_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f201,f87])).

fof(f87,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK1),X1)
      | sK1 = k7_relat_1(sK1,X1) ) ),
    inference(resolution,[],[f27,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f201,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl8_5
  <=> r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f84,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f27,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f157,plain,(
    k11_relat_1(sK1,sK0) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(superposition,[],[f85,f61])).

fof(f61,plain,(
    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f29,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f85,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f27,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f204,plain,
    ( k2_relat_1(sK1) != k11_relat_1(sK1,sK0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl8_6
  <=> k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f320,plain,
    ( ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f218,f60,f278,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK5(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f278,plain,
    ( k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0))
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f274,f271])).

fof(f271,plain,
    ( sK0 = sK3(sK1,sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)))
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f221,f185])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | sK0 = sK3(sK1,X0) )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl8_4
  <=> ! [X0] :
        ( sK0 = sK3(sK1,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f221,plain,
    ( r2_hidden(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f60,f218,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f274,plain,
    ( sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = k1_funct_1(sK1,sK3(sK1,sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0))))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f28,f27,f221,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f28,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f30,f59])).

fof(f30,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f16])).

% (30554)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f218,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ spl8_6 ),
    inference(superposition,[],[f97,f205])).

fof(f205,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f203])).

fof(f97,plain,(
    k1_xboole_0 != k11_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f27,f93,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f93,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f82,f61])).

fof(f82,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f206,plain,
    ( spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f197,f203,f199])).

fof(f197,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f195,f157])).

fof(f195,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(resolution,[],[f162,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f162,plain,(
    ! [X0] :
      ( r2_hidden(sK7(k1_relat_1(sK1),X0),k1_relat_1(sK1))
      | k2_relat_1(sK1) = k9_relat_1(sK1,X0) ) ),
    inference(superposition,[],[f84,f152])).

fof(f152,plain,(
    ! [X0] :
      ( sK1 = k7_relat_1(sK1,X0)
      | r2_hidden(sK7(k1_relat_1(sK1),X0),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f87,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f190,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f28,f182])).

fof(f182,plain,
    ( ~ v1_funct_1(sK1)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl8_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f186,plain,
    ( ~ spl8_2
    | ~ spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f122,f184,f180,f167])).

fof(f167,plain,
    ( spl8_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f122,plain,(
    ! [X0] :
      ( sK0 = sK3(sK1,X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f96,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK0 = X0
      | sK0 = X0
      | sK0 = X0 ) ),
    inference(superposition,[],[f83,f61])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f174,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f27,f169])).

fof(f169,plain,
    ( ~ v1_relat_1(sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:16:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (30548)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.50  % (30557)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (30566)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.51  % (30552)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (30555)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (30572)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (30558)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (30553)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (30574)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (30549)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (30571)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (30566)Refutation not found, incomplete strategy% (30566)------------------------------
% 0.22/0.53  % (30566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30566)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30566)Memory used [KB]: 10618
% 0.22/0.53  % (30566)Time elapsed: 0.123 s
% 0.22/0.53  % (30566)------------------------------
% 0.22/0.53  % (30566)------------------------------
% 0.22/0.53  % (30563)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (30577)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (30564)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (30550)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (30578)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (30551)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (30556)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (30552)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f453,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f174,f186,f190,f206,f320,f452])).
% 0.22/0.54  fof(f452,plain,(
% 0.22/0.54    ~spl8_5 | spl8_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f444])).
% 0.22/0.54  fof(f444,plain,(
% 0.22/0.54    $false | (~spl8_5 | spl8_6)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f204,f424])).
% 0.22/0.54  % (30560)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  fof(f424,plain,(
% 0.22/0.54    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | ~spl8_5),
% 0.22/0.54    inference(backward_demodulation,[],[f157,f423])).
% 0.22/0.54  fof(f423,plain,(
% 0.22/0.54    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) | ~spl8_5),
% 0.22/0.54    inference(superposition,[],[f84,f362])).
% 0.22/0.54  fof(f362,plain,(
% 0.22/0.54    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) | ~spl8_5),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f201,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X1] : (~r1_tarski(k1_relat_1(sK1),X1) | sK1 = k7_relat_1(sK1,X1)) )),
% 0.22/0.54    inference(resolution,[],[f27,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    v1_relat_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.54    inference(negated_conjecture,[],[f13])).
% 0.22/0.54  fof(f13,conjecture,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.22/0.54  fof(f201,plain,(
% 0.22/0.54    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~spl8_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f199])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    spl8_5 <=> r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f27,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    k11_relat_1(sK1,sK0) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.22/0.54    inference(superposition,[],[f85,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.54    inference(definition_unfolding,[],[f29,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f44,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f56,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0))) )),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f27,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f43,f59])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.22/0.54  fof(f204,plain,(
% 0.22/0.54    k2_relat_1(sK1) != k11_relat_1(sK1,sK0) | spl8_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f203])).
% 0.22/0.54  fof(f203,plain,(
% 0.22/0.54    spl8_6 <=> k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.54  fof(f320,plain,(
% 0.22/0.54    ~spl8_4 | ~spl8_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f312])).
% 0.22/0.54  fof(f312,plain,(
% 0.22/0.54    $false | (~spl8_4 | ~spl8_6)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f218,f60,f278,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 0.22/0.54    inference(definition_unfolding,[],[f42,f59])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK5(X0,X1) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 0.22/0.54  fof(f278,plain,(
% 0.22/0.54    k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) | (~spl8_4 | ~spl8_6)),
% 0.22/0.54    inference(backward_demodulation,[],[f274,f271])).
% 0.22/0.54  fof(f271,plain,(
% 0.22/0.54    sK0 = sK3(sK1,sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0))) | (~spl8_4 | ~spl8_6)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f221,f185])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | sK0 = sK3(sK1,X0)) ) | ~spl8_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f184])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    spl8_4 <=> ! [X0] : (sK0 = sK3(sK1,X0) | ~r2_hidden(X0,k2_relat_1(sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.54  fof(f221,plain,(
% 0.22/0.54    r2_hidden(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1)) | ~spl8_6),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f60,f218,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 0.22/0.54    inference(definition_unfolding,[],[f41,f59])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f274,plain,(
% 0.22/0.54    sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = k1_funct_1(sK1,sK3(sK1,sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)))) | ~spl8_6),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f28,f27,f221,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.54    inference(equality_resolution,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    v1_funct_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.22/0.54    inference(definition_unfolding,[],[f30,f59])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  % (30554)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  fof(f218,plain,(
% 0.22/0.54    k1_xboole_0 != k2_relat_1(sK1) | ~spl8_6),
% 0.22/0.54    inference(superposition,[],[f97,f205])).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | ~spl8_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f203])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    k1_xboole_0 != k11_relat_1(sK1,sK0)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f27,f93,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.54    inference(superposition,[],[f82,f61])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X4,X2,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X1,X2))) )),
% 0.22/0.54    inference(equality_resolution,[],[f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k2_enumset1(X4,X4,X1,X2) != X3) )),
% 0.22/0.54    inference(equality_resolution,[],[f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.22/0.54    inference(definition_unfolding,[],[f50,f57])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    spl8_5 | spl8_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f197,f203,f199])).
% 0.22/0.54  fof(f197,plain,(
% 0.22/0.54    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 0.22/0.54    inference(forward_demodulation,[],[f195,f157])).
% 0.22/0.54  fof(f195,plain,(
% 0.22/0.54    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 0.22/0.54    inference(resolution,[],[f162,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK7(k1_relat_1(sK1),X0),k1_relat_1(sK1)) | k2_relat_1(sK1) = k9_relat_1(sK1,X0)) )),
% 0.22/0.54    inference(superposition,[],[f84,f152])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    ( ! [X0] : (sK1 = k7_relat_1(sK1,X0) | r2_hidden(sK7(k1_relat_1(sK1),X0),k1_relat_1(sK1))) )),
% 0.22/0.54    inference(resolution,[],[f87,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f190,plain,(
% 0.22/0.54    spl8_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f187])).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    $false | spl8_3),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f28,f182])).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    ~v1_funct_1(sK1) | spl8_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f180])).
% 0.22/0.54  fof(f180,plain,(
% 0.22/0.54    spl8_3 <=> v1_funct_1(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    ~spl8_2 | ~spl8_3 | spl8_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f122,f184,f180,f167])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    spl8_2 <=> v1_relat_1(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    ( ! [X0] : (sK0 = sK3(sK1,X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 0.22/0.54    inference(resolution,[],[f96,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X2,X0] : (r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.54    inference(equality_resolution,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK0 = X0) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f92])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK0 = X0 | sK0 = X0 | sK0 = X0) )),
% 0.22/0.54    inference(superposition,[],[f83,f61])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.22/0.54    inference(equality_resolution,[],[f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.22/0.54    inference(definition_unfolding,[],[f49,f57])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    spl8_2),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f171])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    $false | spl8_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f27,f169])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    ~v1_relat_1(sK1) | spl8_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f167])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (30552)------------------------------
% 0.22/0.54  % (30552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30552)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (30552)Memory used [KB]: 6396
% 0.22/0.54  % (30552)Time elapsed: 0.143 s
% 0.22/0.54  % (30552)------------------------------
% 0.22/0.54  % (30552)------------------------------
% 0.22/0.54  % (30569)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (30569)Refutation not found, incomplete strategy% (30569)------------------------------
% 0.22/0.55  % (30569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (30569)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (30569)Memory used [KB]: 10746
% 0.22/0.55  % (30569)Time elapsed: 0.150 s
% 0.22/0.55  % (30569)------------------------------
% 0.22/0.55  % (30569)------------------------------
% 0.22/0.55  % (30561)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (30575)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (30570)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (30573)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (30576)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (30562)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (30567)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (30568)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (30547)Success in time 0.202 s
%------------------------------------------------------------------------------
