%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 207 expanded)
%              Number of leaves         :   17 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  179 ( 393 expanded)
%              Number of equality atoms :   45 ( 145 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1070,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f63,f90,f142,f420,f583,f679,f941,f1060])).

fof(f1060,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_16
    | ~ spl2_19
    | ~ spl2_24
    | ~ spl2_30 ),
    inference(avatar_contradiction_clause,[],[f1059])).

fof(f1059,plain,
    ( $false
    | ~ spl2_3
    | spl2_4
    | ~ spl2_16
    | ~ spl2_19
    | ~ spl2_24
    | ~ spl2_30 ),
    inference(subsumption_resolution,[],[f1058,f89])).

fof(f89,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_4
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

% (15475)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f1058,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_19
    | ~ spl2_24
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f1034,f607])).

fof(f607,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f606,f308])).

fof(f308,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f133,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f133,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f62,f75])).

fof(f75,plain,(
    ! [X4,X5,X3] :
      ( r1_xboole_0(X5,k4_xboole_0(X3,X4))
      | ~ r1_xboole_0(X5,X3) ) ),
    inference(superposition,[],[f25,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f62,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_3
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f606,plain,
    ( k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)))),k1_xboole_0)
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f598,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f19,f19])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f598,plain,
    ( k1_xboole_0 = k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),k1_xboole_0)
    | ~ spl2_19 ),
    inference(superposition,[],[f69,f582])).

fof(f582,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f580])).

fof(f580,plain,
    ( spl2_19
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f69,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),k4_xboole_0(X1,X2)) = X1 ),
    inference(superposition,[],[f29,f28])).

fof(f1034,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_16
    | ~ spl2_24
    | ~ spl2_30 ),
    inference(backward_demodulation,[],[f678,f987])).

fof(f987,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl2_16
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f986,f419])).

fof(f419,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl2_16
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f986,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f981,f28])).

fof(f981,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)))
    | ~ spl2_30 ),
    inference(resolution,[],[f914,f31])).

fof(f914,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f912])).

fof(f912,plain,
    ( spl2_30
  <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f678,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0),k1_xboole_0)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f676])).

fof(f676,plain,
    ( spl2_24
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f941,plain,
    ( ~ spl2_2
    | spl2_30 ),
    inference(avatar_contradiction_clause,[],[f940])).

fof(f940,plain,
    ( $false
    | ~ spl2_2
    | spl2_30 ),
    inference(subsumption_resolution,[],[f934,f365])).

fof(f365,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,k4_xboole_0(X0,sK1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f131,f28])).

fof(f131,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,X0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f40,f75])).

fof(f40,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_2
  <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f934,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_30 ),
    inference(resolution,[],[f913,f75])).

fof(f913,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1))
    | spl2_30 ),
    inference(avatar_component_clause,[],[f912])).

fof(f679,plain,
    ( spl2_24
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f159,f139,f676])).

fof(f139,plain,
    ( spl2_6
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f159,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0),k1_xboole_0)
    | ~ spl2_6 ),
    inference(superposition,[],[f29,f141])).

fof(f141,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f583,plain,
    ( spl2_19
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f224,f60,f580])).

fof(f224,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f62,f62,f57])).

fof(f57,plain,(
    ! [X8,X7,X9] :
      ( ~ r1_xboole_0(X7,X9)
      | ~ r1_xboole_0(X7,X8)
      | k1_xboole_0 = k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X8,X9))) ) ),
    inference(resolution,[],[f23,f31])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f420,plain,
    ( spl2_16
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f152,f139,f417])).

fof(f152,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ spl2_6 ),
    inference(superposition,[],[f141,f28])).

fof(f142,plain,
    ( spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f51,f38,f139])).

fof(f51,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f40,f31])).

fof(f90,plain,
    ( ~ spl2_4
    | spl2_1 ),
    inference(avatar_split_clause,[],[f46,f33,f87])).

fof(f33,plain,
    ( spl2_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f46,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f35,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f63,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f48,f60])).

fof(f48,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f27,f30])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f41,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f38])).

fof(f26,plain,(
    r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) ),
    inference(definition_unfolding,[],[f16,f19])).

fof(f16,plain,(
    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f36,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f15,f33])).

fof(f15,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (15476)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.43  % (15468)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.45  % (15464)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.45  % (15469)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (15465)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (15473)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (15463)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (15467)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (15461)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (15462)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (15466)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (15476)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (15474)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f1070,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f36,f41,f63,f90,f142,f420,f583,f679,f941,f1060])).
% 0.21/0.49  fof(f1060,plain,(
% 0.21/0.49    ~spl2_3 | spl2_4 | ~spl2_16 | ~spl2_19 | ~spl2_24 | ~spl2_30),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f1059])).
% 0.21/0.49  fof(f1059,plain,(
% 0.21/0.49    $false | (~spl2_3 | spl2_4 | ~spl2_16 | ~spl2_19 | ~spl2_24 | ~spl2_30)),
% 0.21/0.49    inference(subsumption_resolution,[],[f1058,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl2_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl2_4 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.49  % (15475)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  fof(f1058,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_3 | ~spl2_16 | ~spl2_19 | ~spl2_24 | ~spl2_30)),
% 0.21/0.49    inference(forward_demodulation,[],[f1034,f607])).
% 0.21/0.49  fof(f607,plain,(
% 0.21/0.49    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl2_3 | ~spl2_19)),
% 0.21/0.49    inference(forward_demodulation,[],[f606,f308])).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) ) | ~spl2_3),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f133,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f21,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ) | ~spl2_3),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f62,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (r1_xboole_0(X5,k4_xboole_0(X3,X4)) | ~r1_xboole_0(X5,X3)) )),
% 0.21/0.49    inference(superposition,[],[f25,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f20,f19])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl2_3 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.49  fof(f606,plain,(
% 0.21/0.49    k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)))),k1_xboole_0) | ~spl2_19),
% 0.21/0.49    inference(forward_demodulation,[],[f598,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f18,f19,f19])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.49  fof(f598,plain,(
% 0.21/0.49    k1_xboole_0 = k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),k1_xboole_0) | ~spl2_19),
% 0.21/0.49    inference(superposition,[],[f69,f582])).
% 0.21/0.49  fof(f582,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0))) | ~spl2_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f580])).
% 0.21/0.49  fof(f580,plain,(
% 0.21/0.49    spl2_19 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),k4_xboole_0(X1,X2)) = X1) )),
% 0.21/0.49    inference(superposition,[],[f29,f28])).
% 0.21/0.49  fof(f1034,plain,(
% 0.21/0.49    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl2_16 | ~spl2_24 | ~spl2_30)),
% 0.21/0.49    inference(backward_demodulation,[],[f678,f987])).
% 0.21/0.49  fof(f987,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) | (~spl2_16 | ~spl2_30)),
% 0.21/0.49    inference(forward_demodulation,[],[f986,f419])).
% 0.21/0.49  fof(f419,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~spl2_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f417])).
% 0.21/0.49  fof(f417,plain,(
% 0.21/0.49    spl2_16 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.49  fof(f986,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) | ~spl2_30),
% 0.21/0.49    inference(forward_demodulation,[],[f981,f28])).
% 0.21/0.49  fof(f981,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1))) | ~spl2_30),
% 0.21/0.49    inference(resolution,[],[f914,f31])).
% 0.21/0.49  fof(f914,plain,(
% 0.21/0.49    r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)) | ~spl2_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f912])).
% 0.21/0.49  fof(f912,plain,(
% 0.21/0.49    spl2_30 <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.21/0.49  fof(f678,plain,(
% 0.21/0.49    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0),k1_xboole_0) | ~spl2_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f676])).
% 0.21/0.49  fof(f676,plain,(
% 0.21/0.49    spl2_24 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0),k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.49  fof(f941,plain,(
% 0.21/0.49    ~spl2_2 | spl2_30),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f940])).
% 0.21/0.49  fof(f940,plain,(
% 0.21/0.49    $false | (~spl2_2 | spl2_30)),
% 0.21/0.49    inference(subsumption_resolution,[],[f934,f365])).
% 0.21/0.49  fof(f365,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,k4_xboole_0(X0,sK1)))) ) | ~spl2_2),
% 0.21/0.49    inference(superposition,[],[f131,f28])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,X0))) ) | ~spl2_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f40,f75])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) | ~spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    spl2_2 <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f934,plain,(
% 0.21/0.49    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_30),
% 0.21/0.49    inference(resolution,[],[f913,f75])).
% 0.21/0.49  fof(f913,plain,(
% 0.21/0.49    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)) | spl2_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f912])).
% 0.21/0.49  fof(f679,plain,(
% 0.21/0.49    spl2_24 | ~spl2_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f159,f139,f676])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    spl2_6 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0),k1_xboole_0) | ~spl2_6),
% 0.21/0.49    inference(superposition,[],[f29,f141])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)) | ~spl2_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f139])).
% 0.21/0.49  fof(f583,plain,(
% 0.21/0.49    spl2_19 | ~spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f224,f60,f580])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0))) | ~spl2_3),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f62,f62,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X8,X7,X9] : (~r1_xboole_0(X7,X9) | ~r1_xboole_0(X7,X8) | k1_xboole_0 = k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X8,X9)))) )),
% 0.21/0.49    inference(resolution,[],[f23,f31])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f420,plain,(
% 0.21/0.49    spl2_16 | ~spl2_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f152,f139,f417])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~spl2_6),
% 0.21/0.49    inference(superposition,[],[f141,f28])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    spl2_6 | ~spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f51,f38,f139])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)) | ~spl2_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f40,f31])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ~spl2_4 | spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f33,f87])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    spl2_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl2_1),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f35,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f22,f19])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ~r1_xboole_0(sK0,sK1) | spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f33])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f60])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f27,f30])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f17,f19])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.49    inference(rectify,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f38])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),
% 0.21/0.49    inference(definition_unfolding,[],[f16,f19])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) & ~r1_xboole_0(sK0,sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) & ~r1_xboole_0(sK0,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ~spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f15,f33])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (15476)------------------------------
% 0.21/0.49  % (15476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15476)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (15476)Memory used [KB]: 11513
% 0.21/0.49  % (15476)Time elapsed: 0.065 s
% 0.21/0.49  % (15476)------------------------------
% 0.21/0.49  % (15476)------------------------------
% 0.21/0.49  % (15472)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (15470)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (15460)Success in time 0.137 s
%------------------------------------------------------------------------------
