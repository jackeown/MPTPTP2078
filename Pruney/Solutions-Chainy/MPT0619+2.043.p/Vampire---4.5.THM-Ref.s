%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 268 expanded)
%              Number of leaves         :   16 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  216 ( 600 expanded)
%              Number of equality atoms :  108 ( 358 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f977,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f190,f220,f224,f325,f811])).

fof(f811,plain,
    ( ~ spl8_5
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f803])).

fof(f803,plain,
    ( $false
    | ~ spl8_5
    | spl8_11 ),
    inference(unit_resulting_resolution,[],[f338,f60,f729,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f35,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK5(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f729,plain,
    ( k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0))
    | ~ spl8_5
    | spl8_11 ),
    inference(backward_demodulation,[],[f724,f721])).

fof(f721,plain,
    ( sK0 = sK3(sK1,sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)))
    | ~ spl8_5
    | spl8_11 ),
    inference(unit_resulting_resolution,[],[f390,f219])).

fof(f219,plain,
    ( ! [X0] :
        ( sK0 = sK3(sK1,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl8_5
  <=> ! [X0] :
        ( sK0 = sK3(sK1,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f390,plain,
    ( r2_hidden(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1))
    | spl8_11 ),
    inference(unit_resulting_resolution,[],[f60,f338,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f34,f59])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f724,plain,
    ( sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = k1_funct_1(sK1,sK3(sK1,sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0))))
    | spl8_11 ),
    inference(unit_resulting_resolution,[],[f23,f22,f390,f78])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    k2_relat_1(sK1) != k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f25,f59])).

fof(f25,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f338,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | spl8_11 ),
    inference(unit_resulting_resolution,[],[f22,f287,f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f287,plain,
    ( k1_xboole_0 != k1_relat_1(sK1)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl8_11
  <=> k1_xboole_0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f325,plain,(
    ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f51,f304])).

fof(f304,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_11 ),
    inference(backward_demodulation,[],[f101,f288])).

fof(f288,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f286])).

fof(f101,plain,(
    ~ v1_xboole_0(k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f94,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f94,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f89,f61])).

fof(f61,plain,(
    k1_relat_1(sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f24,f59])).

fof(f24,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,(
    ! [X6,X4,X2,X3,X1] : r2_hidden(X6,k4_enumset1(X6,X6,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X5,X3,X1] :
      ( r2_hidden(X6,X5)
      | k4_enumset1(X6,X6,X1,X2,X3,X4) != X5 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X0 != X6
      | r2_hidden(X6,X5)
      | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X0 != X6
      | r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f224,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f23,f216])).

fof(f216,plain,
    ( ~ v1_funct_1(sK1)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl8_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f220,plain,
    ( ~ spl8_2
    | ~ spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f165,f218,f214,f183])).

fof(f183,plain,
    ( spl8_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f165,plain,(
    ! [X0] :
      ( sK0 = sK3(sK1,X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f99,f79])).

fof(f79,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK0 = X0
      | sK0 = X0
      | sK0 = X0
      | sK0 = X0
      | sK0 = X0 ) ),
    inference(superposition,[],[f90,f61])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X6,k4_enumset1(X0,X0,X1,X2,X3,X4))
      | X1 = X6
      | X2 = X6
      | X3 = X6
      | X4 = X6
      | X0 = X6 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X0 = X6
      | X1 = X6
      | X2 = X6
      | X3 = X6
      | X4 = X6
      | ~ r2_hidden(X6,X5)
      | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X0 = X6
      | X1 = X6
      | X2 = X6
      | X3 = X6
      | X4 = X6
      | ~ r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f190,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f22,f185])).

fof(f185,plain,
    ( ~ v1_relat_1(sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:05:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (23974)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (23998)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.50  % (23990)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.50  % (23981)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (23990)Refutation not found, incomplete strategy% (23990)------------------------------
% 0.22/0.51  % (23990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23992)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (23986)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (23972)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (23975)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (23990)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (23990)Memory used [KB]: 10746
% 0.22/0.52  % (23990)Time elapsed: 0.107 s
% 0.22/0.52  % (23990)------------------------------
% 0.22/0.52  % (23990)------------------------------
% 0.22/0.52  % (23977)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (23971)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (23970)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (23974)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f977,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f190,f220,f224,f325,f811])).
% 0.22/0.53  fof(f811,plain,(
% 0.22/0.53    ~spl8_5 | spl8_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f803])).
% 0.22/0.53  fof(f803,plain,(
% 0.22/0.53    $false | (~spl8_5 | spl8_11)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f338,f60,f729,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f35,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f36,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f52,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f55,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f54,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK5(X0,X1) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 0.22/0.53  fof(f729,plain,(
% 0.22/0.53    k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) | (~spl8_5 | spl8_11)),
% 0.22/0.53    inference(backward_demodulation,[],[f724,f721])).
% 0.22/0.53  fof(f721,plain,(
% 0.22/0.53    sK0 = sK3(sK1,sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0))) | (~spl8_5 | spl8_11)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f390,f219])).
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    ( ! [X0] : (sK0 = sK3(sK1,X0) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl8_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f218])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    spl8_5 <=> ! [X0] : (sK0 = sK3(sK1,X0) | ~r2_hidden(X0,k2_relat_1(sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.53  fof(f390,plain,(
% 0.22/0.53    r2_hidden(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1)) | spl8_11),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f60,f338,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f34,f59])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f724,plain,(
% 0.22/0.53    sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = k1_funct_1(sK1,sK3(sK1,sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)))) | spl8_11),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f23,f22,f390,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    v1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.53    inference(negated_conjecture,[],[f13])).
% 0.22/0.53  fof(f13,conjecture,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    v1_funct_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    k2_relat_1(sK1) != k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.22/0.53    inference(definition_unfolding,[],[f25,f59])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f338,plain,(
% 0.22/0.53    k1_xboole_0 != k2_relat_1(sK1) | spl8_11),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f22,f287,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.53  fof(f287,plain,(
% 0.22/0.53    k1_xboole_0 != k1_relat_1(sK1) | spl8_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f286])).
% 0.22/0.53  fof(f286,plain,(
% 0.22/0.53    spl8_11 <=> k1_xboole_0 = k1_relat_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.53  fof(f325,plain,(
% 0.22/0.53    ~spl8_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f321])).
% 0.22/0.53  fof(f321,plain,(
% 0.22/0.53    $false | ~spl8_11),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f51,f304])).
% 0.22/0.53  fof(f304,plain,(
% 0.22/0.53    ~v1_xboole_0(k1_xboole_0) | ~spl8_11),
% 0.22/0.53    inference(backward_demodulation,[],[f101,f288])).
% 0.22/0.53  fof(f288,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(sK1) | ~spl8_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f286])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ~v1_xboole_0(k1_relat_1(sK1))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f94,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.53    inference(superposition,[],[f89,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    k1_relat_1(sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.53    inference(definition_unfolding,[],[f24,f59])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X3,X1] : (r2_hidden(X6,k4_enumset1(X6,X6,X1,X2,X3,X4))) )),
% 0.22/0.53    inference(equality_resolution,[],[f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X5,X3,X1] : (r2_hidden(X6,X5) | k4_enumset1(X6,X6,X1,X2,X3,X4) != X5) )),
% 0.22/0.53    inference(equality_resolution,[],[f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X0 != X6 | r2_hidden(X6,X5) | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5) )),
% 0.22/0.53    inference(definition_unfolding,[],[f44,f53])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X0 != X6 | r2_hidden(X6,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.53  fof(f224,plain,(
% 0.22/0.53    spl8_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f221])).
% 0.22/0.53  fof(f221,plain,(
% 0.22/0.53    $false | spl8_4),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f23,f216])).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    ~v1_funct_1(sK1) | spl8_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f214])).
% 0.22/0.53  fof(f214,plain,(
% 0.22/0.53    spl8_4 <=> v1_funct_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    ~spl8_2 | ~spl8_4 | spl8_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f165,f218,f214,f183])).
% 0.22/0.53  fof(f183,plain,(
% 0.22/0.53    spl8_2 <=> v1_relat_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    ( ! [X0] : (sK0 = sK3(sK1,X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 0.22/0.53    inference(resolution,[],[f99,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X2,X0] : (r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK0 = X0) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK0 = X0 | sK0 = X0 | sK0 = X0 | sK0 = X0 | sK0 = X0) )),
% 0.22/0.53    inference(superposition,[],[f90,f61])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X3,X1] : (~r2_hidden(X6,k4_enumset1(X0,X0,X1,X2,X3,X4)) | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | X0 = X6) )),
% 0.22/0.53    inference(equality_resolution,[],[f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | ~r2_hidden(X6,X5) | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5) )),
% 0.22/0.53    inference(definition_unfolding,[],[f43,f53])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | ~r2_hidden(X6,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    spl8_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f187])).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    $false | spl8_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f22,f185])).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    ~v1_relat_1(sK1) | spl8_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f183])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (23974)------------------------------
% 0.22/0.53  % (23974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23974)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (23974)Memory used [KB]: 6652
% 0.22/0.53  % (23974)Time elapsed: 0.100 s
% 0.22/0.53  % (23974)------------------------------
% 0.22/0.53  % (23974)------------------------------
% 0.22/0.54  % (23969)Success in time 0.166 s
%------------------------------------------------------------------------------
