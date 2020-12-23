%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 177 expanded)
%              Number of leaves         :   27 (  85 expanded)
%              Depth                    :    7
%              Number of atoms          :  240 ( 469 expanded)
%              Number of equality atoms :   42 (  75 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (18019)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% (18020)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
fof(f593,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f36,f41,f45,f49,f53,f57,f61,f67,f75,f80,f85,f99,f104,f109,f154,f162,f286,f460,f582,f592])).

fof(f592,plain,
    ( ~ spl4_15
    | ~ spl4_21
    | spl4_87 ),
    inference(avatar_contradiction_clause,[],[f591])).

fof(f591,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_21
    | spl4_87 ),
    inference(subsumption_resolution,[],[f588,f103])).

fof(f103,plain,
    ( sK3 = k4_xboole_0(sK3,sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_15
  <=> sK3 = k4_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f588,plain,
    ( sK3 != k4_xboole_0(sK3,sK1)
    | ~ spl4_21
    | spl4_87 ),
    inference(superposition,[],[f581,f153])).

fof(f153,plain,
    ( ! [X4] : k4_xboole_0(sK3,k2_xboole_0(sK0,X4)) = k4_xboole_0(sK3,X4)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl4_21
  <=> ! [X4] : k4_xboole_0(sK3,k2_xboole_0(sK0,X4)) = k4_xboole_0(sK3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f581,plain,
    ( sK3 != k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | spl4_87 ),
    inference(avatar_component_clause,[],[f579])).

fof(f579,plain,
    ( spl4_87
  <=> sK3 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f582,plain,
    ( ~ spl4_87
    | spl4_10
    | ~ spl4_69 ),
    inference(avatar_split_clause,[],[f573,f458,f64,f579])).

fof(f64,plain,
    ( spl4_10
  <=> r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f458,plain,
    ( spl4_69
  <=> ! [X1] :
        ( sK3 != k4_xboole_0(sK3,X1)
        | r1_xboole_0(k2_xboole_0(sK2,X1),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f573,plain,
    ( sK3 != k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | spl4_10
    | ~ spl4_69 ),
    inference(resolution,[],[f459,f66])).

fof(f66,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f64])).

fof(f459,plain,
    ( ! [X1] :
        ( r1_xboole_0(k2_xboole_0(sK2,X1),sK3)
        | sK3 != k4_xboole_0(sK3,X1) )
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f458])).

fof(f460,plain,
    ( spl4_69
    | ~ spl4_6
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f450,f284,f47,f458])).

fof(f47,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f284,plain,
    ( spl4_45
  <=> ! [X2] :
        ( sK3 != k4_xboole_0(sK3,X2)
        | r1_xboole_0(sK3,k2_xboole_0(sK2,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f450,plain,
    ( ! [X1] :
        ( sK3 != k4_xboole_0(sK3,X1)
        | r1_xboole_0(k2_xboole_0(sK2,X1),sK3) )
    | ~ spl4_6
    | ~ spl4_45 ),
    inference(resolution,[],[f285,f48])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f285,plain,
    ( ! [X2] :
        ( r1_xboole_0(sK3,k2_xboole_0(sK2,X2))
        | sK3 != k4_xboole_0(sK3,X2) )
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f284])).

fof(f286,plain,
    ( spl4_45
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f272,f160,f51,f284])).

fof(f51,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f160,plain,
    ( spl4_23
  <=> ! [X6] : k4_xboole_0(sK3,k2_xboole_0(sK2,X6)) = k4_xboole_0(sK3,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f272,plain,
    ( ! [X2] :
        ( sK3 != k4_xboole_0(sK3,X2)
        | r1_xboole_0(sK3,k2_xboole_0(sK2,X2)) )
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(superposition,[],[f52,f161])).

fof(f161,plain,
    ( ! [X6] : k4_xboole_0(sK3,k2_xboole_0(sK2,X6)) = k4_xboole_0(sK3,X6)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f160])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | r1_xboole_0(X0,X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f162,plain,
    ( spl4_23
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f140,f106,f59,f160])).

fof(f59,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f106,plain,
    ( spl4_16
  <=> sK3 = k4_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f140,plain,
    ( ! [X6] : k4_xboole_0(sK3,k2_xboole_0(sK2,X6)) = k4_xboole_0(sK3,X6)
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(superposition,[],[f60,f108])).

fof(f108,plain,
    ( sK3 = k4_xboole_0(sK3,sK2)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f60,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f154,plain,
    ( spl4_21
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f138,f96,f59,f152])).

fof(f96,plain,
    ( spl4_14
  <=> sK3 = k4_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f138,plain,
    ( ! [X4] : k4_xboole_0(sK3,k2_xboole_0(sK0,X4)) = k4_xboole_0(sK3,X4)
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(superposition,[],[f60,f98])).

fof(f98,plain,
    ( sK3 = k4_xboole_0(sK3,sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f109,plain,
    ( spl4_16
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f91,f72,f55,f106])).

fof(f55,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f72,plain,
    ( spl4_11
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f91,plain,
    ( sK3 = k4_xboole_0(sK3,sK2)
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(resolution,[],[f56,f74])).

fof(f74,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f104,plain,
    ( spl4_15
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f90,f77,f55,f101])).

fof(f77,plain,
    ( spl4_12
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f90,plain,
    ( sK3 = k4_xboole_0(sK3,sK1)
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(resolution,[],[f56,f79])).

fof(f79,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f99,plain,
    ( spl4_14
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f89,f82,f55,f96])).

fof(f82,plain,
    ( spl4_13
  <=> r1_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f89,plain,
    ( sK3 = k4_xboole_0(sK3,sK0)
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(resolution,[],[f56,f84])).

fof(f84,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f82])).

fof(f85,plain,
    ( spl4_13
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f70,f47,f38,f82])).

fof(f38,plain,
    ( spl4_4
  <=> r1_xboole_0(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f70,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f48,f40])).

fof(f40,plain,
    ( r1_xboole_0(sK0,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f80,plain,
    ( spl4_12
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f69,f47,f33,f77])).

fof(f33,plain,
    ( spl4_3
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f69,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f48,f35])).

fof(f35,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f75,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f68,f47,f28,f72])).

fof(f28,plain,
    ( spl4_2
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f68,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f48,f30])).

fof(f30,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f67,plain,
    ( ~ spl4_10
    | spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f62,f43,f23,f64])).

fof(f23,plain,
    ( spl4_1
  <=> r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f43,plain,
    ( spl4_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f62,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3)
    | spl4_1
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f25,f44])).

fof(f44,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f25,plain,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f61,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f21,f59])).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f57,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f19,f55])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f53,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f20,f51])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f18,f47])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f45,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f17,f43])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f41,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f13,f38])).

fof(f13,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    & r1_xboole_0(sK2,sK3)
    & r1_xboole_0(sK1,sK3)
    & r1_xboole_0(sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
        & r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
   => ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
      & r1_xboole_0(sK2,sK3)
      & r1_xboole_0(sK1,sK3)
      & r1_xboole_0(sK0,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          & r1_xboole_0(X1,X3)
          & r1_xboole_0(X0,X3) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).

fof(f36,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f14,f33])).

fof(f14,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f15,f28])).

fof(f15,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f16,f23])).

fof(f16,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (18018)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (18017)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (18012)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.44  % (18013)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.44  % (18014)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.45  % (18017)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  % (18019)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.46  % (18020)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.46  fof(f593,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f26,f31,f36,f41,f45,f49,f53,f57,f61,f67,f75,f80,f85,f99,f104,f109,f154,f162,f286,f460,f582,f592])).
% 0.21/0.46  fof(f592,plain,(
% 0.21/0.46    ~spl4_15 | ~spl4_21 | spl4_87),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f591])).
% 0.21/0.46  fof(f591,plain,(
% 0.21/0.46    $false | (~spl4_15 | ~spl4_21 | spl4_87)),
% 0.21/0.46    inference(subsumption_resolution,[],[f588,f103])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    sK3 = k4_xboole_0(sK3,sK1) | ~spl4_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f101])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl4_15 <=> sK3 = k4_xboole_0(sK3,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.46  fof(f588,plain,(
% 0.21/0.46    sK3 != k4_xboole_0(sK3,sK1) | (~spl4_21 | spl4_87)),
% 0.21/0.46    inference(superposition,[],[f581,f153])).
% 0.21/0.46  fof(f153,plain,(
% 0.21/0.46    ( ! [X4] : (k4_xboole_0(sK3,k2_xboole_0(sK0,X4)) = k4_xboole_0(sK3,X4)) ) | ~spl4_21),
% 0.21/0.46    inference(avatar_component_clause,[],[f152])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    spl4_21 <=> ! [X4] : k4_xboole_0(sK3,k2_xboole_0(sK0,X4)) = k4_xboole_0(sK3,X4)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.46  fof(f581,plain,(
% 0.21/0.46    sK3 != k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | spl4_87),
% 0.21/0.46    inference(avatar_component_clause,[],[f579])).
% 0.21/0.46  fof(f579,plain,(
% 0.21/0.46    spl4_87 <=> sK3 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 0.21/0.46  fof(f582,plain,(
% 0.21/0.46    ~spl4_87 | spl4_10 | ~spl4_69),
% 0.21/0.46    inference(avatar_split_clause,[],[f573,f458,f64,f579])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    spl4_10 <=> r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.46  fof(f458,plain,(
% 0.21/0.46    spl4_69 <=> ! [X1] : (sK3 != k4_xboole_0(sK3,X1) | r1_xboole_0(k2_xboole_0(sK2,X1),sK3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 0.21/0.46  fof(f573,plain,(
% 0.21/0.46    sK3 != k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | (spl4_10 | ~spl4_69)),
% 0.21/0.46    inference(resolution,[],[f459,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ~r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3) | spl4_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f64])).
% 0.21/0.46  fof(f459,plain,(
% 0.21/0.46    ( ! [X1] : (r1_xboole_0(k2_xboole_0(sK2,X1),sK3) | sK3 != k4_xboole_0(sK3,X1)) ) | ~spl4_69),
% 0.21/0.46    inference(avatar_component_clause,[],[f458])).
% 0.21/0.46  fof(f460,plain,(
% 0.21/0.46    spl4_69 | ~spl4_6 | ~spl4_45),
% 0.21/0.46    inference(avatar_split_clause,[],[f450,f284,f47,f458])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    spl4_6 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.46  fof(f284,plain,(
% 0.21/0.46    spl4_45 <=> ! [X2] : (sK3 != k4_xboole_0(sK3,X2) | r1_xboole_0(sK3,k2_xboole_0(sK2,X2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.21/0.46  fof(f450,plain,(
% 0.21/0.46    ( ! [X1] : (sK3 != k4_xboole_0(sK3,X1) | r1_xboole_0(k2_xboole_0(sK2,X1),sK3)) ) | (~spl4_6 | ~spl4_45)),
% 0.21/0.46    inference(resolution,[],[f285,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl4_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f47])).
% 0.21/0.46  fof(f285,plain,(
% 0.21/0.46    ( ! [X2] : (r1_xboole_0(sK3,k2_xboole_0(sK2,X2)) | sK3 != k4_xboole_0(sK3,X2)) ) | ~spl4_45),
% 0.21/0.46    inference(avatar_component_clause,[],[f284])).
% 0.21/0.46  fof(f286,plain,(
% 0.21/0.46    spl4_45 | ~spl4_7 | ~spl4_23),
% 0.21/0.46    inference(avatar_split_clause,[],[f272,f160,f51,f284])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl4_7 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.46  fof(f160,plain,(
% 0.21/0.46    spl4_23 <=> ! [X6] : k4_xboole_0(sK3,k2_xboole_0(sK2,X6)) = k4_xboole_0(sK3,X6)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.46  fof(f272,plain,(
% 0.21/0.46    ( ! [X2] : (sK3 != k4_xboole_0(sK3,X2) | r1_xboole_0(sK3,k2_xboole_0(sK2,X2))) ) | (~spl4_7 | ~spl4_23)),
% 0.21/0.46    inference(superposition,[],[f52,f161])).
% 0.21/0.46  fof(f161,plain,(
% 0.21/0.46    ( ! [X6] : (k4_xboole_0(sK3,k2_xboole_0(sK2,X6)) = k4_xboole_0(sK3,X6)) ) | ~spl4_23),
% 0.21/0.46    inference(avatar_component_clause,[],[f160])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) ) | ~spl4_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f51])).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    spl4_23 | ~spl4_9 | ~spl4_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f140,f106,f59,f160])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    spl4_9 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    spl4_16 <=> sK3 = k4_xboole_0(sK3,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.46  fof(f140,plain,(
% 0.21/0.46    ( ! [X6] : (k4_xboole_0(sK3,k2_xboole_0(sK2,X6)) = k4_xboole_0(sK3,X6)) ) | (~spl4_9 | ~spl4_16)),
% 0.21/0.46    inference(superposition,[],[f60,f108])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    sK3 = k4_xboole_0(sK3,sK2) | ~spl4_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f106])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl4_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f59])).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    spl4_21 | ~spl4_9 | ~spl4_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f138,f96,f59,f152])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    spl4_14 <=> sK3 = k4_xboole_0(sK3,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    ( ! [X4] : (k4_xboole_0(sK3,k2_xboole_0(sK0,X4)) = k4_xboole_0(sK3,X4)) ) | (~spl4_9 | ~spl4_14)),
% 0.21/0.46    inference(superposition,[],[f60,f98])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    sK3 = k4_xboole_0(sK3,sK0) | ~spl4_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f96])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    spl4_16 | ~spl4_8 | ~spl4_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f91,f72,f55,f106])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl4_8 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    spl4_11 <=> r1_xboole_0(sK3,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    sK3 = k4_xboole_0(sK3,sK2) | (~spl4_8 | ~spl4_11)),
% 0.21/0.46    inference(resolution,[],[f56,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    r1_xboole_0(sK3,sK2) | ~spl4_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f72])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl4_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f55])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    spl4_15 | ~spl4_8 | ~spl4_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f90,f77,f55,f101])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl4_12 <=> r1_xboole_0(sK3,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    sK3 = k4_xboole_0(sK3,sK1) | (~spl4_8 | ~spl4_12)),
% 0.21/0.46    inference(resolution,[],[f56,f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    r1_xboole_0(sK3,sK1) | ~spl4_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f77])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    spl4_14 | ~spl4_8 | ~spl4_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f89,f82,f55,f96])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    spl4_13 <=> r1_xboole_0(sK3,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    sK3 = k4_xboole_0(sK3,sK0) | (~spl4_8 | ~spl4_13)),
% 0.21/0.46    inference(resolution,[],[f56,f84])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    r1_xboole_0(sK3,sK0) | ~spl4_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f82])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl4_13 | ~spl4_4 | ~spl4_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f70,f47,f38,f82])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    spl4_4 <=> r1_xboole_0(sK0,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    r1_xboole_0(sK3,sK0) | (~spl4_4 | ~spl4_6)),
% 0.21/0.46    inference(resolution,[],[f48,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    r1_xboole_0(sK0,sK3) | ~spl4_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f38])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    spl4_12 | ~spl4_3 | ~spl4_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f69,f47,f33,f77])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    spl4_3 <=> r1_xboole_0(sK1,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    r1_xboole_0(sK3,sK1) | (~spl4_3 | ~spl4_6)),
% 0.21/0.46    inference(resolution,[],[f48,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    r1_xboole_0(sK1,sK3) | ~spl4_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f33])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    spl4_11 | ~spl4_2 | ~spl4_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f68,f47,f28,f72])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    spl4_2 <=> r1_xboole_0(sK2,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    r1_xboole_0(sK3,sK2) | (~spl4_2 | ~spl4_6)),
% 0.21/0.46    inference(resolution,[],[f48,f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    r1_xboole_0(sK2,sK3) | ~spl4_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f28])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ~spl4_10 | spl4_1 | ~spl4_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f62,f43,f23,f64])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    spl4_1 <=> r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    spl4_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ~r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3) | (spl4_1 | ~spl4_5)),
% 0.21/0.46    inference(forward_demodulation,[],[f25,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl4_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f43])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) | spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f23])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    spl4_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f59])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    spl4_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f55])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    spl4_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f51])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    spl4_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f18,f47])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    spl4_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f43])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f13,f38])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    r1_xboole_0(sK0,sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => (~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3))),
% 0.21/0.46    inference(flattening,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & (r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    spl4_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f14,f33])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    r1_xboole_0(sK1,sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    spl4_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f15,f28])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    r1_xboole_0(sK2,sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ~spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f16,f23])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (18017)------------------------------
% 0.21/0.46  % (18017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (18017)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (18017)Memory used [KB]: 10874
% 0.21/0.46  % (18017)Time elapsed: 0.025 s
% 0.21/0.46  % (18017)------------------------------
% 0.21/0.46  % (18017)------------------------------
% 0.21/0.46  % (18021)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.46  % (18011)Success in time 0.108 s
%------------------------------------------------------------------------------
