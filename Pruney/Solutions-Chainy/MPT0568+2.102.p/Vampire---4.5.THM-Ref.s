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
% DateTime   : Thu Dec  3 12:50:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   98 ( 114 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f45,f70,f107,f137])).

fof(f137,plain,
    ( spl5_1
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl5_1
    | ~ spl5_10 ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl5_1
    | ~ spl5_10 ),
    inference(superposition,[],[f33,f106])).

fof(f106,plain,
    ( ! [X3] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_10
  <=> ! [X3] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f33,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl5_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f107,plain,
    ( spl5_10
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f99,f68,f105])).

fof(f68,plain,
    ( spl5_6
  <=> ! [X3,X4] : ~ r2_hidden(X3,k10_relat_1(k1_xboole_0,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f99,plain,
    ( ! [X3] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X3)
    | ~ spl5_6 ),
    inference(resolution,[],[f69,f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f69,plain,
    ( ! [X4,X3] : ~ r2_hidden(X3,k10_relat_1(k1_xboole_0,X4))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f70,plain,
    ( spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f66,f42,f68])).

fof(f42,plain,
    ( spl5_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f66,plain,
    ( ! [X4,X3] : ~ r2_hidden(X3,k10_relat_1(k1_xboole_0,X4))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f65,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f21,f19])).

fof(f19,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f65,plain,
    ( ! [X4,X3] :
        ( r2_hidden(k4_tarski(X3,sK4(X3,X4,k1_xboole_0)),k1_xboole_0)
        | ~ r2_hidden(X3,k10_relat_1(k1_xboole_0,X4)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f27,f44])).

fof(f44,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f45,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f40,f36,f42])).

fof(f36,plain,
    ( spl5_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f40,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_2 ),
    inference(superposition,[],[f18,f38])).

fof(f38,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f39,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f34,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:15:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (13943)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.42  % (13943)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f138,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f34,f39,f45,f70,f107,f137])).
% 0.21/0.42  fof(f137,plain,(
% 0.21/0.42    spl5_1 | ~spl5_10),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f136])).
% 0.21/0.42  fof(f136,plain,(
% 0.21/0.42    $false | (spl5_1 | ~spl5_10)),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f133])).
% 0.21/0.42  fof(f133,plain,(
% 0.21/0.42    k1_xboole_0 != k1_xboole_0 | (spl5_1 | ~spl5_10)),
% 0.21/0.42    inference(superposition,[],[f33,f106])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    ( ! [X3] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X3)) ) | ~spl5_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f105])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    spl5_10 <=> ! [X3] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl5_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    spl5_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    spl5_10 | ~spl5_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f99,f68,f105])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl5_6 <=> ! [X3,X4] : ~r2_hidden(X3,k10_relat_1(k1_xboole_0,X4))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    ( ! [X3] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X3)) ) | ~spl5_6),
% 0.21/0.42    inference(resolution,[],[f69,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    ( ! [X4,X3] : (~r2_hidden(X3,k10_relat_1(k1_xboole_0,X4))) ) | ~spl5_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f68])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl5_6 | ~spl5_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f66,f42,f68])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl5_3 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    ( ! [X4,X3] : (~r2_hidden(X3,k10_relat_1(k1_xboole_0,X4))) ) | ~spl5_3),
% 0.21/0.42    inference(subsumption_resolution,[],[f65,f46])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(resolution,[],[f21,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(rectify,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ( ! [X4,X3] : (r2_hidden(k4_tarski(X3,sK4(X3,X4,k1_xboole_0)),k1_xboole_0) | ~r2_hidden(X3,k10_relat_1(k1_xboole_0,X4))) ) | ~spl5_3),
% 0.21/0.42    inference(resolution,[],[f27,f44])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    v1_relat_1(k1_xboole_0) | ~spl5_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl5_3 | ~spl5_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f40,f36,f42])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl5_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    v1_relat_1(k1_xboole_0) | ~spl5_2),
% 0.21/0.42    inference(superposition,[],[f18,f38])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl5_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f36])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    spl5_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f36])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ~spl5_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f31])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,negated_conjecture,(
% 0.21/0.42    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    inference(negated_conjecture,[],[f8])).
% 0.21/0.42  fof(f8,conjecture,(
% 0.21/0.42    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (13943)------------------------------
% 0.21/0.42  % (13943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (13943)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (13943)Memory used [KB]: 10618
% 0.21/0.42  % (13943)Time elapsed: 0.008 s
% 0.21/0.42  % (13943)------------------------------
% 0.21/0.42  % (13943)------------------------------
% 0.21/0.43  % (13941)Success in time 0.066 s
%------------------------------------------------------------------------------
