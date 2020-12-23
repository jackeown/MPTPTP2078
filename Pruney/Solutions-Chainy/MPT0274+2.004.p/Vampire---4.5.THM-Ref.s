%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:20 EST 2020

% Result     : Theorem 2.49s
% Output     : Refutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  251 ( 930 expanded)
%              Number of leaves         :   47 ( 340 expanded)
%              Depth                    :   12
%              Number of atoms          :  528 (1955 expanded)
%              Number of equality atoms :   52 ( 310 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f781,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f86,f98,f156,f158,f524,f532,f544,f550,f551,f554,f555,f560,f565,f580,f590,f592,f599,f601,f608,f642,f643,f651,f656,f661,f666,f671,f676,f678,f683,f688,f689,f694,f695,f697,f702,f703,f714,f719,f745,f747,f749,f754,f755,f756,f757,f763,f764,f769,f770,f776,f777,f778,f779,f780])).

fof(f780,plain,
    ( spl4_11
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f774,f557,f562])).

fof(f562,plain,
    ( spl4_11
  <=> r1_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f557,plain,
    ( spl4_10
  <=> r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f774,plain,
    ( r1_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f558,f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f56,f121])).

fof(f121,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k3_xboole_0(X3,X2))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f55,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f558,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f557])).

fof(f779,plain,
    ( ~ spl4_3
    | spl4_8 ),
    inference(avatar_split_clause,[],[f722,f529,f82])).

fof(f82,plain,
    ( spl4_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f529,plain,
    ( spl4_8
  <=> r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f722,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl4_8 ),
    inference(resolution,[],[f530,f271])).

fof(f271,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_xboole_0(X1,k2_tarski(X0,X2)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f212,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f212,plain,(
    ! [X4,X5,X3] : ~ r2_hidden(X3,k5_xboole_0(X4,k3_xboole_0(X4,k2_tarski(X3,X5)))) ),
    inference(resolution,[],[f202,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f202,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(resolution,[],[f195,f68])).

fof(f68,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f530,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f529])).

fof(f778,plain,
    ( ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f773,f557,f82])).

fof(f773,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f558,f54])).

fof(f777,plain,
    ( ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f772,f557,f77])).

fof(f77,plain,
    ( spl4_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f772,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f558,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X1,X0),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f54,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f776,plain,
    ( ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f775])).

fof(f775,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f772,f78])).

fof(f78,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f770,plain,
    ( spl4_31
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f736,f95,f766])).

fof(f766,plain,
    ( spl4_31
  <=> r1_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f95,plain,
    ( spl4_4
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f736,plain,
    ( r1_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1))
    | ~ spl4_4 ),
    inference(superposition,[],[f57,f96])).

fof(f96,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f57,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f769,plain,
    ( spl4_31
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f750,f95,f766])).

fof(f750,plain,
    ( r1_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f737,f52])).

fof(f737,plain,
    ( r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | ~ spl4_4 ),
    inference(superposition,[],[f100,f96])).

fof(f100,plain,(
    ! [X2,X1] : r1_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f57,f52])).

fof(f764,plain,
    ( spl4_30
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f738,f95,f760])).

fof(f760,plain,
    ( spl4_30
  <=> r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f738,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | ~ spl4_4 ),
    inference(superposition,[],[f208,f96])).

fof(f208,plain,(
    ! [X8,X9] : r1_xboole_0(k5_xboole_0(X8,X9),k3_xboole_0(X8,X9)) ),
    inference(resolution,[],[f195,f57])).

fof(f763,plain,
    ( spl4_30
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f751,f95,f760])).

fof(f751,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f739,f52])).

fof(f739,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k3_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)))
    | ~ spl4_4 ),
    inference(superposition,[],[f209,f96])).

fof(f209,plain,(
    ! [X10,X11] : r1_xboole_0(k5_xboole_0(X10,X11),k3_xboole_0(X11,X10)) ),
    inference(resolution,[],[f195,f100])).

fof(f757,plain,
    ( ~ spl4_11
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f725,f541,f562])).

fof(f541,plain,
    ( spl4_9
  <=> r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f725,plain,
    ( ~ r1_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ spl4_9 ),
    inference(resolution,[],[f543,f55])).

fof(f543,plain,
    ( r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f541])).

fof(f756,plain,
    ( spl4_11
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f728,f95,f562])).

fof(f728,plain,
    ( r1_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ spl4_4 ),
    inference(superposition,[],[f203,f96])).

fof(f203,plain,(
    ! [X2,X3] : r1_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))) ),
    inference(resolution,[],[f195,f91])).

fof(f91,plain,(
    ! [X4,X3] : r1_xboole_0(k5_xboole_0(X3,k3_xboole_0(X4,X3)),X4) ),
    inference(superposition,[],[f68,f52])).

fof(f755,plain,
    ( ~ spl4_10
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f724,f541,f557])).

fof(f724,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl4_9 ),
    inference(resolution,[],[f543,f121])).

fof(f754,plain,
    ( spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f729,f95,f557])).

fof(f729,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl4_4 ),
    inference(superposition,[],[f91,f96])).

fof(f749,plain,
    ( ~ spl4_4
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f748])).

fof(f748,plain,
    ( $false
    | ~ spl4_4
    | spl4_10 ),
    inference(subsumption_resolution,[],[f729,f559])).

fof(f559,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f557])).

fof(f747,plain,
    ( ~ spl4_4
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f746])).

fof(f746,plain,
    ( $false
    | ~ spl4_4
    | spl4_11 ),
    inference(subsumption_resolution,[],[f728,f564])).

fof(f564,plain,
    ( ~ r1_xboole_0(sK2,k2_tarski(sK0,sK1))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f562])).

fof(f745,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f744])).

fof(f744,plain,
    ( $false
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f727,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f727,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1))
    | ~ spl4_4
    | spl4_5 ),
    inference(backward_demodulation,[],[f155,f96])).

fof(f155,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl4_5
  <=> r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f719,plain,
    ( spl4_29
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f705,f668,f716])).

fof(f716,plain,
    ( spl4_29
  <=> k5_xboole_0(sK2,k2_tarski(sK0,sK0)) = k3_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f668,plain,
    ( spl4_21
  <=> r1_tarski(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f705,plain,
    ( k5_xboole_0(sK2,k2_tarski(sK0,sK0)) = k3_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),sK2)
    | ~ spl4_21 ),
    inference(resolution,[],[f670,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f670,plain,
    ( r1_tarski(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),sK2)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f668])).

fof(f714,plain,
    ( spl4_27
    | ~ spl4_28
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f704,f668,f711,f707])).

fof(f707,plain,
    ( spl4_27
  <=> sK2 = k5_xboole_0(sK2,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f711,plain,
    ( spl4_28
  <=> r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f704,plain,
    ( ~ r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK0)))
    | sK2 = k5_xboole_0(sK2,k2_tarski(sK0,sK0))
    | ~ spl4_21 ),
    inference(resolution,[],[f670,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f703,plain,
    ( ~ spl4_16
    | spl4_26
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f637,f577,f699,f645])).

fof(f645,plain,
    ( spl4_16
  <=> r1_xboole_0(sK2,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f699,plain,
    ( spl4_26
  <=> r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f577,plain,
    ( spl4_12
  <=> k2_tarski(sK0,sK0) = k3_xboole_0(sK2,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f637,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))
    | ~ r1_xboole_0(sK2,k2_tarski(sK0,sK0))
    | ~ spl4_12 ),
    inference(superposition,[],[f257,f579])).

fof(f579,plain,
    ( k2_tarski(sK0,sK0) = k3_xboole_0(sK2,k2_tarski(sK0,sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f577])).

fof(f257,plain,(
    ! [X8,X7] :
      ( r1_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,X8))
      | ~ r1_xboole_0(X7,X8) ) ),
    inference(resolution,[],[f197,f55])).

fof(f197,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,X0),X0)
      | r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f56,f53])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f702,plain,
    ( ~ spl4_23
    | spl4_26
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f636,f577,f699,f680])).

fof(f680,plain,
    ( spl4_23
  <=> r1_xboole_0(k2_tarski(sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f636,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))
    | ~ r1_xboole_0(k2_tarski(sK0,sK0),sK2)
    | ~ spl4_12 ),
    inference(superposition,[],[f256,f579])).

fof(f256,plain,(
    ! [X6,X5] :
      ( r1_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X5,X6))
      | ~ r1_xboole_0(X6,X5) ) ),
    inference(resolution,[],[f197,f121])).

fof(f697,plain,
    ( spl4_20
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f696,f577,f663])).

fof(f663,plain,
    ( spl4_20
  <=> r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f696,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f635,f51])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f635,plain,
    ( r1_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK2),k2_tarski(sK0,sK0))
    | ~ spl4_12 ),
    inference(superposition,[],[f209,f579])).

fof(f695,plain,
    ( spl4_20
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f634,f577,f663])).

fof(f634,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | ~ spl4_12 ),
    inference(superposition,[],[f208,f579])).

fof(f694,plain,
    ( spl4_25
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f633,f577,f691])).

fof(f691,plain,
    ( spl4_25
  <=> r1_xboole_0(sK2,k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f633,plain,
    ( r1_xboole_0(sK2,k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)))
    | ~ spl4_12 ),
    inference(superposition,[],[f203,f579])).

fof(f689,plain,
    ( spl4_19
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f632,f577,f658])).

fof(f658,plain,
    ( spl4_19
  <=> r1_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(sK2,k2_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f632,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(sK2,k2_tarski(sK0,sK0)))
    | ~ spl4_12 ),
    inference(superposition,[],[f202,f579])).

fof(f688,plain,
    ( spl4_23
    | spl4_24
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f631,f577,f685,f680])).

fof(f685,plain,
    ( spl4_24
  <=> r2_hidden(sK3(k2_tarski(sK0,sK0),sK2),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f631,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK0),sK2),k2_tarski(sK0,sK0))
    | r1_xboole_0(k2_tarski(sK0,sK0),sK2)
    | ~ spl4_12 ),
    inference(superposition,[],[f198,f579])).

fof(f198,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(X1,X2),k3_xboole_0(X2,X1))
      | r1_xboole_0(X1,X2) ) ),
    inference(superposition,[],[f56,f52])).

fof(f683,plain,
    ( ~ spl4_23
    | spl4_17
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f630,f577,f649,f680])).

fof(f649,plain,
    ( spl4_17
  <=> ! [X0] : ~ r2_hidden(X0,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f630,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK0,sK0))
        | ~ r1_xboole_0(k2_tarski(sK0,sK0),sK2) )
    | ~ spl4_12 ),
    inference(superposition,[],[f121,f579])).

fof(f678,plain,
    ( spl4_19
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f677,f577,f658])).

fof(f677,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(sK2,k2_tarski(sK0,sK0)))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f629,f51])).

fof(f629,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK0),sK2))
    | ~ spl4_12 ),
    inference(superposition,[],[f100,f579])).

fof(f676,plain,
    ( spl4_22
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f628,f577,f673])).

fof(f673,plain,
    ( spl4_22
  <=> r1_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f628,plain,
    ( r1_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),sK2)
    | ~ spl4_12 ),
    inference(superposition,[],[f91,f579])).

fof(f671,plain,
    ( spl4_21
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f626,f577,f668])).

fof(f626,plain,
    ( r1_tarski(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),sK2)
    | ~ spl4_12 ),
    inference(superposition,[],[f69,f579])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f666,plain,
    ( spl4_20
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f625,f577,f663])).

fof(f625,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | ~ spl4_12 ),
    inference(superposition,[],[f68,f579])).

fof(f661,plain,
    ( spl4_19
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f624,f577,f658])).

fof(f624,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(sK2,k2_tarski(sK0,sK0)))
    | ~ spl4_12 ),
    inference(superposition,[],[f57,f579])).

fof(f656,plain,
    ( spl4_16
    | spl4_18
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f623,f577,f653,f645])).

fof(f653,plain,
    ( spl4_18
  <=> r2_hidden(sK3(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f623,plain,
    ( r2_hidden(sK3(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | r1_xboole_0(sK2,k2_tarski(sK0,sK0))
    | ~ spl4_12 ),
    inference(superposition,[],[f56,f579])).

fof(f651,plain,
    ( ~ spl4_16
    | spl4_17
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f622,f577,f649,f645])).

fof(f622,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK0,sK0))
        | ~ r1_xboole_0(sK2,k2_tarski(sK0,sK0)) )
    | ~ spl4_12 ),
    inference(superposition,[],[f55,f579])).

fof(f643,plain,
    ( ~ spl4_15
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f621,f577,f639])).

fof(f639,plain,
    ( spl4_15
  <=> r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f621,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK0)))
    | ~ spl4_12 ),
    inference(superposition,[],[f211,f579])).

fof(f211,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X2,X0)))) ),
    inference(resolution,[],[f202,f118])).

fof(f642,plain,
    ( ~ spl4_15
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f620,f577,f639])).

fof(f620,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK0)))
    | ~ spl4_12 ),
    inference(superposition,[],[f212,f579])).

fof(f608,plain,
    ( ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f606])).

fof(f606,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f83,f604])).

fof(f604,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl4_13 ),
    inference(resolution,[],[f585,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f55,f53])).

fof(f585,plain,
    ( r1_xboole_0(sK2,sK2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f583])).

fof(f583,plain,
    ( spl4_13
  <=> r1_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f83,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f601,plain,
    ( spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f600,f73,f95])).

fof(f73,plain,
    ( spl4_1
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f600,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f75,f52])).

fof(f75,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f599,plain,
    ( spl4_2
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f598])).

fof(f598,plain,
    ( $false
    | spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f594,f79])).

fof(f79,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f594,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl4_9 ),
    inference(resolution,[],[f543,f264])).

fof(f264,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(X4,k2_tarski(X5,X3)))
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f211,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f592,plain,
    ( ~ spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f591,f73,f95])).

fof(f591,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl4_1 ),
    inference(forward_demodulation,[],[f74,f52])).

fof(f74,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f590,plain,
    ( spl4_13
    | spl4_14
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f581,f82,f587,f583])).

fof(f587,plain,
    ( spl4_14
  <=> k2_tarski(sK0,sK3(sK2,sK2)) = k3_xboole_0(sK2,k2_tarski(sK0,sK3(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f581,plain,
    ( k2_tarski(sK0,sK3(sK2,sK2)) = k3_xboole_0(sK2,k2_tarski(sK0,sK3(sK2,sK2)))
    | r1_xboole_0(sK2,sK2)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f575,f48])).

fof(f575,plain,
    ( k2_tarski(sK3(sK2,sK2),sK0) = k3_xboole_0(sK2,k2_tarski(sK3(sK2,sK2),sK0))
    | r1_xboole_0(sK2,sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f567,f197])).

fof(f567,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | k2_tarski(X0,sK0) = k3_xboole_0(sK2,k2_tarski(X0,sK0)) )
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f566,f52])).

fof(f566,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | k2_tarski(X0,sK0) = k3_xboole_0(k2_tarski(X0,sK0),sK2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f83,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1)
      | k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f580,plain,
    ( spl4_12
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f574,f82,f577])).

fof(f574,plain,
    ( k2_tarski(sK0,sK0) = k3_xboole_0(sK2,k2_tarski(sK0,sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f567,f83])).

fof(f565,plain,
    ( ~ spl4_11
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f547,f529,f562])).

fof(f547,plain,
    ( ~ r1_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ spl4_8 ),
    inference(resolution,[],[f531,f55])).

fof(f531,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f529])).

fof(f560,plain,
    ( ~ spl4_10
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f546,f529,f557])).

fof(f546,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl4_8 ),
    inference(resolution,[],[f531,f121])).

fof(f555,plain,
    ( spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f552,f73,f95])).

fof(f552,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f75,f52])).

fof(f554,plain,
    ( ~ spl4_1
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f553])).

fof(f553,plain,
    ( $false
    | ~ spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f552,f97])).

fof(f97,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f551,plain,
    ( spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f545,f529,f82])).

fof(f545,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_8 ),
    inference(resolution,[],[f531,f272])).

fof(f272,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(X4,k2_tarski(X3,X5)))
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f212,f42])).

fof(f550,plain,
    ( spl4_3
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f549])).

fof(f549,plain,
    ( $false
    | spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f545,f84])).

fof(f84,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f544,plain,
    ( spl4_9
    | spl4_7 ),
    inference(avatar_split_clause,[],[f539,f521,f541])).

fof(f521,plain,
    ( spl4_7
  <=> r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f539,plain,
    ( r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl4_7 ),
    inference(subsumption_resolution,[],[f537,f126])).

fof(f126,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(superposition,[],[f123,f48])).

fof(f123,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f58,f70])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f537,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl4_7 ),
    inference(resolution,[],[f523,f43])).

fof(f523,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f521])).

fof(f532,plain,
    ( spl4_8
    | spl4_6 ),
    inference(avatar_split_clause,[],[f527,f517,f529])).

fof(f517,plain,
    ( spl4_6
  <=> r2_hidden(sK0,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f527,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl4_6 ),
    inference(subsumption_resolution,[],[f525,f123])).

fof(f525,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl4_6 ),
    inference(resolution,[],[f519,f43])).

fof(f519,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f517])).

fof(f524,plain,
    ( ~ spl4_6
    | ~ spl4_7
    | spl4_5 ),
    inference(avatar_split_clause,[],[f510,f153,f521,f517])).

fof(f510,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | ~ r2_hidden(sK0,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | spl4_5 ),
    inference(resolution,[],[f60,f155])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f158,plain,
    ( ~ spl4_5
    | spl4_4 ),
    inference(avatar_split_clause,[],[f157,f95,f153])).

fof(f157,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | spl4_4 ),
    inference(subsumption_resolution,[],[f146,f90])).

fof(f90,plain,(
    ! [X2,X1] : r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(superposition,[],[f69,f52])).

fof(f146,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | ~ r1_tarski(k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1))
    | spl4_4 ),
    inference(extensionality_resolution,[],[f63,f97])).

fof(f156,plain,
    ( ~ spl4_5
    | spl4_4 ),
    inference(avatar_split_clause,[],[f151,f95,f153])).

fof(f151,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | spl4_4 ),
    inference(subsumption_resolution,[],[f145,f90])).

fof(f145,plain,
    ( ~ r1_tarski(k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1))
    | ~ r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | spl4_4 ),
    inference(extensionality_resolution,[],[f63,f97])).

fof(f98,plain,
    ( ~ spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f89,f73,f95])).

fof(f89,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl4_1 ),
    inference(backward_demodulation,[],[f74,f52])).

fof(f86,plain,
    ( ~ spl4_1
    | spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f67,f82,f77,f73])).

fof(f67,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f37,f44])).

fof(f37,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f85,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f66,f82,f73])).

fof(f66,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f38,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f65,f77,f73])).

fof(f65,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f39,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n023.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 15:16:06 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.46  % (6324)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.18/0.47  % (6318)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.18/0.48  % (6306)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.18/0.50  % (6313)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.18/0.50  % (6322)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.18/0.51  % (6312)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.51  % (6311)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.51  % (6314)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.18/0.51  % (6309)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.18/0.51  % (6308)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.18/0.51  % (6333)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.18/0.52  % (6307)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.18/0.52  % (6315)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.18/0.52  % (6307)Refutation not found, incomplete strategy% (6307)------------------------------
% 0.18/0.52  % (6307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.52  % (6307)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.52  
% 0.18/0.52  % (6307)Memory used [KB]: 1663
% 0.18/0.52  % (6307)Time elapsed: 0.133 s
% 0.18/0.52  % (6307)------------------------------
% 0.18/0.52  % (6307)------------------------------
% 0.18/0.52  % (6334)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.18/0.52  % (6322)Refutation not found, incomplete strategy% (6322)------------------------------
% 0.18/0.52  % (6322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.52  % (6334)Refutation not found, incomplete strategy% (6334)------------------------------
% 0.18/0.52  % (6334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.52  % (6334)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.52  
% 0.18/0.52  % (6334)Memory used [KB]: 10746
% 0.18/0.52  % (6334)Time elapsed: 0.139 s
% 0.18/0.52  % (6334)------------------------------
% 0.18/0.52  % (6334)------------------------------
% 0.18/0.52  % (6322)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.52  
% 0.18/0.52  % (6322)Memory used [KB]: 10618
% 0.18/0.52  % (6322)Time elapsed: 0.141 s
% 0.18/0.52  % (6322)------------------------------
% 0.18/0.52  % (6322)------------------------------
% 0.18/0.52  % (6326)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.18/0.52  % (6330)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.18/0.52  % (6316)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.18/0.53  % (6316)Refutation not found, incomplete strategy% (6316)------------------------------
% 0.18/0.53  % (6316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.53  % (6316)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.53  
% 0.18/0.53  % (6316)Memory used [KB]: 10746
% 0.18/0.53  % (6316)Time elapsed: 0.150 s
% 0.18/0.53  % (6316)------------------------------
% 0.18/0.53  % (6316)------------------------------
% 0.18/0.53  % (6325)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.18/0.53  % (6329)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.18/0.53  % (6323)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.18/0.53  % (6323)Refutation not found, incomplete strategy% (6323)------------------------------
% 0.18/0.53  % (6323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.53  % (6323)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.53  
% 0.18/0.53  % (6323)Memory used [KB]: 1663
% 0.18/0.53  % (6323)Time elapsed: 0.148 s
% 0.18/0.53  % (6323)------------------------------
% 0.18/0.53  % (6323)------------------------------
% 0.18/0.53  % (6320)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.18/0.53  % (6310)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.18/0.53  % (6320)Refutation not found, incomplete strategy% (6320)------------------------------
% 0.18/0.53  % (6320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.53  % (6320)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.53  
% 0.18/0.53  % (6320)Memory used [KB]: 1663
% 0.18/0.53  % (6320)Time elapsed: 0.137 s
% 0.18/0.53  % (6320)------------------------------
% 0.18/0.53  % (6320)------------------------------
% 0.18/0.53  % (6335)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.18/0.53  % (6335)Refutation not found, incomplete strategy% (6335)------------------------------
% 0.18/0.53  % (6335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.53  % (6335)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.53  
% 0.18/0.53  % (6335)Memory used [KB]: 1663
% 0.18/0.53  % (6335)Time elapsed: 0.120 s
% 0.18/0.53  % (6335)------------------------------
% 0.18/0.53  % (6335)------------------------------
% 0.18/0.54  % (6317)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.18/0.54  % (6319)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.18/0.54  % (6327)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.18/0.54  % (6321)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.18/0.54  % (6331)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.18/0.54  % (6332)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.18/0.54  % (6317)Refutation not found, incomplete strategy% (6317)------------------------------
% 0.18/0.54  % (6317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.54  % (6332)Refutation not found, incomplete strategy% (6332)------------------------------
% 0.18/0.54  % (6332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (6328)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.42/0.55  % (6317)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (6317)Memory used [KB]: 6140
% 1.42/0.55  % (6317)Time elapsed: 0.161 s
% 1.42/0.55  % (6317)------------------------------
% 1.42/0.55  % (6317)------------------------------
% 1.42/0.55  % (6332)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (6332)Memory used [KB]: 6268
% 1.42/0.55  % (6332)Time elapsed: 0.171 s
% 1.42/0.55  % (6332)------------------------------
% 1.42/0.55  % (6332)------------------------------
% 1.74/0.65  % (6339)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.23/0.66  % (6336)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.23/0.66  % (6309)Refutation not found, incomplete strategy% (6309)------------------------------
% 2.23/0.66  % (6309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.66  % (6309)Termination reason: Refutation not found, incomplete strategy
% 2.23/0.66  
% 2.23/0.66  % (6309)Memory used [KB]: 6140
% 2.23/0.66  % (6309)Time elapsed: 0.278 s
% 2.23/0.66  % (6309)------------------------------
% 2.23/0.66  % (6309)------------------------------
% 2.23/0.67  % (6342)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.23/0.67  % (6337)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.23/0.67  % (6338)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.23/0.67  % (6340)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.23/0.68  % (6338)Refutation not found, incomplete strategy% (6338)------------------------------
% 2.23/0.68  % (6338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.68  % (6338)Termination reason: Refutation not found, incomplete strategy
% 2.23/0.68  
% 2.23/0.68  % (6338)Memory used [KB]: 6140
% 2.23/0.68  % (6338)Time elapsed: 0.110 s
% 2.23/0.68  % (6338)------------------------------
% 2.23/0.68  % (6338)------------------------------
% 2.23/0.68  % (6344)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.23/0.69  % (6341)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.49/0.69  % (6340)Refutation not found, incomplete strategy% (6340)------------------------------
% 2.49/0.69  % (6340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.49/0.70  % (6340)Termination reason: Refutation not found, incomplete strategy
% 2.49/0.70  
% 2.49/0.70  % (6340)Memory used [KB]: 10618
% 2.49/0.70  % (6340)Time elapsed: 0.142 s
% 2.49/0.70  % (6340)------------------------------
% 2.49/0.70  % (6340)------------------------------
% 2.49/0.71  % (6343)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.49/0.71  % (6306)Refutation found. Thanks to Tanya!
% 2.49/0.71  % SZS status Theorem for theBenchmark
% 2.49/0.71  % SZS output start Proof for theBenchmark
% 2.49/0.71  fof(f781,plain,(
% 2.49/0.71    $false),
% 2.49/0.71    inference(avatar_sat_refutation,[],[f80,f85,f86,f98,f156,f158,f524,f532,f544,f550,f551,f554,f555,f560,f565,f580,f590,f592,f599,f601,f608,f642,f643,f651,f656,f661,f666,f671,f676,f678,f683,f688,f689,f694,f695,f697,f702,f703,f714,f719,f745,f747,f749,f754,f755,f756,f757,f763,f764,f769,f770,f776,f777,f778,f779,f780])).
% 2.49/0.71  fof(f780,plain,(
% 2.49/0.71    spl4_11 | ~spl4_10),
% 2.49/0.71    inference(avatar_split_clause,[],[f774,f557,f562])).
% 2.49/0.71  fof(f562,plain,(
% 2.49/0.71    spl4_11 <=> r1_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.49/0.71  fof(f557,plain,(
% 2.49/0.71    spl4_10 <=> r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.49/0.71  fof(f774,plain,(
% 2.49/0.71    r1_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~spl4_10),
% 2.49/0.71    inference(resolution,[],[f558,f195])).
% 2.49/0.71  fof(f195,plain,(
% 2.49/0.71    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | r1_xboole_0(X0,X1)) )),
% 2.49/0.71    inference(resolution,[],[f56,f121])).
% 2.49/0.71  fof(f121,plain,(
% 2.49/0.71    ( ! [X4,X2,X3] : (~r2_hidden(X4,k3_xboole_0(X3,X2)) | ~r1_xboole_0(X2,X3)) )),
% 2.49/0.71    inference(superposition,[],[f55,f52])).
% 2.49/0.71  fof(f52,plain,(
% 2.49/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f1])).
% 2.49/0.71  fof(f1,axiom,(
% 2.49/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.49/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.49/0.71  fof(f55,plain,(
% 2.49/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f35])).
% 2.49/0.71  fof(f35,plain,(
% 2.49/0.71    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.49/0.71    inference(ennf_transformation,[],[f29])).
% 2.49/0.71  fof(f29,plain,(
% 2.49/0.71    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.49/0.71    inference(rectify,[],[f5])).
% 2.49/0.71  fof(f5,axiom,(
% 2.49/0.71    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.49/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.49/0.71  fof(f56,plain,(
% 2.49/0.71    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f35])).
% 2.49/0.71  fof(f558,plain,(
% 2.49/0.71    r1_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl4_10),
% 2.49/0.71    inference(avatar_component_clause,[],[f557])).
% 2.49/0.71  fof(f779,plain,(
% 2.49/0.71    ~spl4_3 | spl4_8),
% 2.49/0.71    inference(avatar_split_clause,[],[f722,f529,f82])).
% 2.49/0.71  fof(f82,plain,(
% 2.49/0.71    spl4_3 <=> r2_hidden(sK0,sK2)),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.49/0.71  fof(f529,plain,(
% 2.49/0.71    spl4_8 <=> r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.49/0.71  fof(f722,plain,(
% 2.49/0.71    ~r2_hidden(sK0,sK2) | spl4_8),
% 2.49/0.71    inference(resolution,[],[f530,f271])).
% 2.49/0.71  fof(f271,plain,(
% 2.49/0.71    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_xboole_0(X1,k2_tarski(X0,X2))) | ~r2_hidden(X0,X1)) )),
% 2.49/0.71    inference(resolution,[],[f212,f43])).
% 2.49/0.71  fof(f43,plain,(
% 2.49/0.71    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f31])).
% 2.49/0.71  fof(f31,plain,(
% 2.49/0.71    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.49/0.71    inference(ennf_transformation,[],[f4])).
% 2.49/0.71  fof(f4,axiom,(
% 2.49/0.71    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.49/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.49/0.71  fof(f212,plain,(
% 2.49/0.71    ( ! [X4,X5,X3] : (~r2_hidden(X3,k5_xboole_0(X4,k3_xboole_0(X4,k2_tarski(X3,X5))))) )),
% 2.49/0.71    inference(resolution,[],[f202,f54])).
% 2.49/0.71  fof(f54,plain,(
% 2.49/0.71    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f34])).
% 2.49/0.71  fof(f34,plain,(
% 2.49/0.71    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.49/0.71    inference(ennf_transformation,[],[f25])).
% 2.49/0.71  fof(f25,axiom,(
% 2.49/0.71    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.49/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 2.49/0.71  fof(f202,plain,(
% 2.49/0.71    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.49/0.71    inference(resolution,[],[f195,f68])).
% 2.49/0.71  fof(f68,plain,(
% 2.49/0.71    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.49/0.71    inference(definition_unfolding,[],[f45,f44])).
% 2.49/0.71  fof(f44,plain,(
% 2.49/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.49/0.71    inference(cnf_transformation,[],[f9])).
% 2.49/0.71  fof(f9,axiom,(
% 2.49/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.49/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.49/0.71  fof(f45,plain,(
% 2.49/0.71    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f14])).
% 2.49/0.71  fof(f14,axiom,(
% 2.49/0.71    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.49/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.49/0.71  fof(f530,plain,(
% 2.49/0.71    ~r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl4_8),
% 2.49/0.71    inference(avatar_component_clause,[],[f529])).
% 2.49/0.71  fof(f778,plain,(
% 2.49/0.71    ~spl4_3 | ~spl4_10),
% 2.49/0.71    inference(avatar_split_clause,[],[f773,f557,f82])).
% 2.49/0.71  fof(f773,plain,(
% 2.49/0.71    ~r2_hidden(sK0,sK2) | ~spl4_10),
% 2.49/0.71    inference(resolution,[],[f558,f54])).
% 2.49/0.71  fof(f777,plain,(
% 2.49/0.71    ~spl4_2 | ~spl4_10),
% 2.49/0.71    inference(avatar_split_clause,[],[f772,f557,f77])).
% 2.49/0.71  fof(f77,plain,(
% 2.49/0.71    spl4_2 <=> r2_hidden(sK1,sK2)),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.49/0.71  fof(f772,plain,(
% 2.49/0.71    ~r2_hidden(sK1,sK2) | ~spl4_10),
% 2.49/0.71    inference(resolution,[],[f558,f118])).
% 2.49/0.71  fof(f118,plain,(
% 2.49/0.71    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X1,X0),X2) | ~r2_hidden(X0,X2)) )),
% 2.49/0.71    inference(superposition,[],[f54,f48])).
% 2.49/0.71  fof(f48,plain,(
% 2.49/0.71    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f16])).
% 2.49/0.71  fof(f16,axiom,(
% 2.49/0.71    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.49/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.49/0.71  fof(f776,plain,(
% 2.49/0.71    ~spl4_2 | ~spl4_10),
% 2.49/0.71    inference(avatar_contradiction_clause,[],[f775])).
% 2.49/0.71  fof(f775,plain,(
% 2.49/0.71    $false | (~spl4_2 | ~spl4_10)),
% 2.49/0.71    inference(subsumption_resolution,[],[f772,f78])).
% 2.49/0.71  fof(f78,plain,(
% 2.49/0.71    r2_hidden(sK1,sK2) | ~spl4_2),
% 2.49/0.71    inference(avatar_component_clause,[],[f77])).
% 2.49/0.71  fof(f770,plain,(
% 2.49/0.71    spl4_31 | ~spl4_4),
% 2.49/0.71    inference(avatar_split_clause,[],[f736,f95,f766])).
% 2.49/0.71  fof(f766,plain,(
% 2.49/0.71    spl4_31 <=> r1_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1))),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 2.49/0.71  fof(f95,plain,(
% 2.49/0.71    spl4_4 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.49/0.71  fof(f736,plain,(
% 2.49/0.71    r1_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1)) | ~spl4_4),
% 2.49/0.71    inference(superposition,[],[f57,f96])).
% 2.49/0.71  fof(f96,plain,(
% 2.49/0.71    k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl4_4),
% 2.49/0.71    inference(avatar_component_clause,[],[f95])).
% 2.49/0.71  fof(f57,plain,(
% 2.49/0.71    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 2.49/0.71    inference(cnf_transformation,[],[f8])).
% 2.49/0.71  fof(f8,axiom,(
% 2.49/0.71    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.49/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 2.49/0.71  fof(f769,plain,(
% 2.49/0.71    spl4_31 | ~spl4_4),
% 2.49/0.71    inference(avatar_split_clause,[],[f750,f95,f766])).
% 2.49/0.71  fof(f750,plain,(
% 2.49/0.71    r1_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1)) | ~spl4_4),
% 2.49/0.71    inference(forward_demodulation,[],[f737,f52])).
% 2.49/0.71  fof(f737,plain,(
% 2.49/0.71    r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | ~spl4_4),
% 2.49/0.71    inference(superposition,[],[f100,f96])).
% 2.49/0.71  fof(f100,plain,(
% 2.49/0.71    ( ! [X2,X1] : (r1_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X1,X2))) )),
% 2.49/0.71    inference(superposition,[],[f57,f52])).
% 2.49/0.71  fof(f764,plain,(
% 2.49/0.71    spl4_30 | ~spl4_4),
% 2.49/0.71    inference(avatar_split_clause,[],[f738,f95,f760])).
% 2.49/0.71  fof(f760,plain,(
% 2.49/0.71    spl4_30 <=> r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 2.49/0.71  fof(f738,plain,(
% 2.49/0.71    r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | ~spl4_4),
% 2.49/0.71    inference(superposition,[],[f208,f96])).
% 2.49/0.71  fof(f208,plain,(
% 2.49/0.71    ( ! [X8,X9] : (r1_xboole_0(k5_xboole_0(X8,X9),k3_xboole_0(X8,X9))) )),
% 2.49/0.71    inference(resolution,[],[f195,f57])).
% 2.49/0.71  fof(f763,plain,(
% 2.49/0.71    spl4_30 | ~spl4_4),
% 2.49/0.71    inference(avatar_split_clause,[],[f751,f95,f760])).
% 2.49/0.71  fof(f751,plain,(
% 2.49/0.71    r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | ~spl4_4),
% 2.49/0.71    inference(forward_demodulation,[],[f739,f52])).
% 2.49/0.71  fof(f739,plain,(
% 2.49/0.71    r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k3_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))) | ~spl4_4),
% 2.49/0.71    inference(superposition,[],[f209,f96])).
% 2.49/0.71  fof(f209,plain,(
% 2.49/0.71    ( ! [X10,X11] : (r1_xboole_0(k5_xboole_0(X10,X11),k3_xboole_0(X11,X10))) )),
% 2.49/0.71    inference(resolution,[],[f195,f100])).
% 2.49/0.71  fof(f757,plain,(
% 2.49/0.71    ~spl4_11 | ~spl4_9),
% 2.49/0.71    inference(avatar_split_clause,[],[f725,f541,f562])).
% 2.49/0.71  fof(f541,plain,(
% 2.49/0.71    spl4_9 <=> r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.49/0.71  fof(f725,plain,(
% 2.49/0.71    ~r1_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~spl4_9),
% 2.49/0.71    inference(resolution,[],[f543,f55])).
% 2.49/0.71  fof(f543,plain,(
% 2.49/0.71    r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl4_9),
% 2.49/0.71    inference(avatar_component_clause,[],[f541])).
% 2.49/0.71  fof(f756,plain,(
% 2.49/0.71    spl4_11 | ~spl4_4),
% 2.49/0.71    inference(avatar_split_clause,[],[f728,f95,f562])).
% 2.49/0.71  fof(f728,plain,(
% 2.49/0.71    r1_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~spl4_4),
% 2.49/0.71    inference(superposition,[],[f203,f96])).
% 2.49/0.71  fof(f203,plain,(
% 2.49/0.71    ( ! [X2,X3] : (r1_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))) )),
% 2.49/0.71    inference(resolution,[],[f195,f91])).
% 2.49/0.71  fof(f91,plain,(
% 2.49/0.71    ( ! [X4,X3] : (r1_xboole_0(k5_xboole_0(X3,k3_xboole_0(X4,X3)),X4)) )),
% 2.49/0.71    inference(superposition,[],[f68,f52])).
% 2.49/0.71  fof(f755,plain,(
% 2.49/0.71    ~spl4_10 | ~spl4_9),
% 2.49/0.71    inference(avatar_split_clause,[],[f724,f541,f557])).
% 2.49/0.71  fof(f724,plain,(
% 2.49/0.71    ~r1_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl4_9),
% 2.49/0.71    inference(resolution,[],[f543,f121])).
% 2.49/0.71  fof(f754,plain,(
% 2.49/0.71    spl4_10 | ~spl4_4),
% 2.49/0.71    inference(avatar_split_clause,[],[f729,f95,f557])).
% 2.49/0.71  fof(f729,plain,(
% 2.49/0.71    r1_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl4_4),
% 2.49/0.71    inference(superposition,[],[f91,f96])).
% 2.49/0.71  fof(f749,plain,(
% 2.49/0.71    ~spl4_4 | spl4_10),
% 2.49/0.71    inference(avatar_contradiction_clause,[],[f748])).
% 2.49/0.71  fof(f748,plain,(
% 2.49/0.71    $false | (~spl4_4 | spl4_10)),
% 2.49/0.71    inference(subsumption_resolution,[],[f729,f559])).
% 2.49/0.71  fof(f559,plain,(
% 2.49/0.71    ~r1_xboole_0(k2_tarski(sK0,sK1),sK2) | spl4_10),
% 2.49/0.71    inference(avatar_component_clause,[],[f557])).
% 2.49/0.71  fof(f747,plain,(
% 2.49/0.71    ~spl4_4 | spl4_11),
% 2.49/0.71    inference(avatar_contradiction_clause,[],[f746])).
% 2.49/0.71  fof(f746,plain,(
% 2.49/0.71    $false | (~spl4_4 | spl4_11)),
% 2.49/0.71    inference(subsumption_resolution,[],[f728,f564])).
% 2.49/0.71  fof(f564,plain,(
% 2.49/0.71    ~r1_xboole_0(sK2,k2_tarski(sK0,sK1)) | spl4_11),
% 2.49/0.71    inference(avatar_component_clause,[],[f562])).
% 2.49/0.71  fof(f745,plain,(
% 2.49/0.71    ~spl4_4 | spl4_5),
% 2.49/0.71    inference(avatar_contradiction_clause,[],[f744])).
% 2.49/0.71  fof(f744,plain,(
% 2.49/0.71    $false | (~spl4_4 | spl4_5)),
% 2.49/0.71    inference(subsumption_resolution,[],[f727,f70])).
% 2.49/0.71  fof(f70,plain,(
% 2.49/0.71    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.49/0.71    inference(equality_resolution,[],[f62])).
% 2.49/0.71  fof(f62,plain,(
% 2.49/0.71    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.49/0.71    inference(cnf_transformation,[],[f7])).
% 2.49/0.71  fof(f7,axiom,(
% 2.49/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.49/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.49/0.71  fof(f727,plain,(
% 2.49/0.71    ~r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) | (~spl4_4 | spl4_5)),
% 2.49/0.71    inference(backward_demodulation,[],[f155,f96])).
% 2.49/0.71  fof(f155,plain,(
% 2.49/0.71    ~r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | spl4_5),
% 2.49/0.71    inference(avatar_component_clause,[],[f153])).
% 2.49/0.71  fof(f153,plain,(
% 2.49/0.71    spl4_5 <=> r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.49/0.71  fof(f719,plain,(
% 2.49/0.71    spl4_29 | ~spl4_21),
% 2.49/0.71    inference(avatar_split_clause,[],[f705,f668,f716])).
% 2.49/0.71  fof(f716,plain,(
% 2.49/0.71    spl4_29 <=> k5_xboole_0(sK2,k2_tarski(sK0,sK0)) = k3_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),sK2)),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.49/0.71  fof(f668,plain,(
% 2.49/0.71    spl4_21 <=> r1_tarski(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),sK2)),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.49/0.71  fof(f705,plain,(
% 2.49/0.71    k5_xboole_0(sK2,k2_tarski(sK0,sK0)) = k3_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),sK2) | ~spl4_21),
% 2.49/0.71    inference(resolution,[],[f670,f64])).
% 2.49/0.71  fof(f64,plain,(
% 2.49/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.49/0.71    inference(cnf_transformation,[],[f36])).
% 2.49/0.71  fof(f36,plain,(
% 2.49/0.71    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.49/0.71    inference(ennf_transformation,[],[f11])).
% 2.49/0.71  fof(f11,axiom,(
% 2.49/0.71    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.49/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.49/0.71  fof(f670,plain,(
% 2.49/0.71    r1_tarski(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),sK2) | ~spl4_21),
% 2.49/0.71    inference(avatar_component_clause,[],[f668])).
% 2.49/0.71  fof(f714,plain,(
% 2.49/0.71    spl4_27 | ~spl4_28 | ~spl4_21),
% 2.49/0.71    inference(avatar_split_clause,[],[f704,f668,f711,f707])).
% 2.49/0.71  fof(f707,plain,(
% 2.49/0.71    spl4_27 <=> sK2 = k5_xboole_0(sK2,k2_tarski(sK0,sK0))),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.49/0.71  fof(f711,plain,(
% 2.49/0.71    spl4_28 <=> r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK0)))),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 2.49/0.71  fof(f704,plain,(
% 2.49/0.71    ~r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK0))) | sK2 = k5_xboole_0(sK2,k2_tarski(sK0,sK0)) | ~spl4_21),
% 2.49/0.71    inference(resolution,[],[f670,f63])).
% 2.49/0.71  fof(f63,plain,(
% 2.49/0.71    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.49/0.71    inference(cnf_transformation,[],[f7])).
% 2.49/0.71  fof(f703,plain,(
% 2.49/0.71    ~spl4_16 | spl4_26 | ~spl4_12),
% 2.49/0.71    inference(avatar_split_clause,[],[f637,f577,f699,f645])).
% 2.49/0.71  fof(f645,plain,(
% 2.49/0.71    spl4_16 <=> r1_xboole_0(sK2,k2_tarski(sK0,sK0))),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.49/0.71  fof(f699,plain,(
% 2.49/0.71    spl4_26 <=> r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 2.49/0.71  fof(f577,plain,(
% 2.49/0.71    spl4_12 <=> k2_tarski(sK0,sK0) = k3_xboole_0(sK2,k2_tarski(sK0,sK0))),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.49/0.71  fof(f637,plain,(
% 2.49/0.71    r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) | ~r1_xboole_0(sK2,k2_tarski(sK0,sK0)) | ~spl4_12),
% 2.49/0.71    inference(superposition,[],[f257,f579])).
% 2.49/0.71  fof(f579,plain,(
% 2.49/0.71    k2_tarski(sK0,sK0) = k3_xboole_0(sK2,k2_tarski(sK0,sK0)) | ~spl4_12),
% 2.49/0.71    inference(avatar_component_clause,[],[f577])).
% 2.49/0.71  fof(f257,plain,(
% 2.49/0.71    ( ! [X8,X7] : (r1_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,X8)) | ~r1_xboole_0(X7,X8)) )),
% 2.49/0.71    inference(resolution,[],[f197,f55])).
% 2.49/0.71  fof(f197,plain,(
% 2.49/0.71    ( ! [X0] : (r2_hidden(sK3(X0,X0),X0) | r1_xboole_0(X0,X0)) )),
% 2.49/0.71    inference(superposition,[],[f56,f53])).
% 2.49/0.71  fof(f53,plain,(
% 2.49/0.71    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.49/0.71    inference(cnf_transformation,[],[f28])).
% 2.49/0.71  fof(f28,plain,(
% 2.49/0.71    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.49/0.71    inference(rectify,[],[f3])).
% 2.49/0.71  fof(f3,axiom,(
% 2.49/0.71    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.49/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.49/0.71  fof(f702,plain,(
% 2.49/0.71    ~spl4_23 | spl4_26 | ~spl4_12),
% 2.49/0.71    inference(avatar_split_clause,[],[f636,f577,f699,f680])).
% 2.49/0.71  fof(f680,plain,(
% 2.49/0.71    spl4_23 <=> r1_xboole_0(k2_tarski(sK0,sK0),sK2)),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 2.49/0.71  fof(f636,plain,(
% 2.49/0.71    r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) | ~r1_xboole_0(k2_tarski(sK0,sK0),sK2) | ~spl4_12),
% 2.49/0.71    inference(superposition,[],[f256,f579])).
% 2.49/0.71  fof(f256,plain,(
% 2.49/0.71    ( ! [X6,X5] : (r1_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X5,X6)) | ~r1_xboole_0(X6,X5)) )),
% 2.49/0.71    inference(resolution,[],[f197,f121])).
% 2.49/0.71  fof(f697,plain,(
% 2.49/0.71    spl4_20 | ~spl4_12),
% 2.49/0.71    inference(avatar_split_clause,[],[f696,f577,f663])).
% 2.49/0.71  fof(f663,plain,(
% 2.49/0.71    spl4_20 <=> r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.49/0.71  fof(f696,plain,(
% 2.49/0.71    r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | ~spl4_12),
% 2.49/0.71    inference(forward_demodulation,[],[f635,f51])).
% 2.49/0.71  fof(f51,plain,(
% 2.49/0.71    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f2])).
% 2.49/0.71  fof(f2,axiom,(
% 2.49/0.71    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.49/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.49/0.72  fof(f635,plain,(
% 2.49/0.72    r1_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK2),k2_tarski(sK0,sK0)) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f209,f579])).
% 2.49/0.72  fof(f695,plain,(
% 2.49/0.72    spl4_20 | ~spl4_12),
% 2.49/0.72    inference(avatar_split_clause,[],[f634,f577,f663])).
% 2.49/0.72  fof(f634,plain,(
% 2.49/0.72    r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f208,f579])).
% 2.49/0.72  fof(f694,plain,(
% 2.49/0.72    spl4_25 | ~spl4_12),
% 2.49/0.72    inference(avatar_split_clause,[],[f633,f577,f691])).
% 2.49/0.72  fof(f691,plain,(
% 2.49/0.72    spl4_25 <=> r1_xboole_0(sK2,k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)))),
% 2.49/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.49/0.72  fof(f633,plain,(
% 2.49/0.72    r1_xboole_0(sK2,k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f203,f579])).
% 2.49/0.72  fof(f689,plain,(
% 2.49/0.72    spl4_19 | ~spl4_12),
% 2.49/0.72    inference(avatar_split_clause,[],[f632,f577,f658])).
% 2.49/0.72  fof(f658,plain,(
% 2.49/0.72    spl4_19 <=> r1_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(sK2,k2_tarski(sK0,sK0)))),
% 2.49/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.49/0.72  fof(f632,plain,(
% 2.49/0.72    r1_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(sK2,k2_tarski(sK0,sK0))) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f202,f579])).
% 2.49/0.72  fof(f688,plain,(
% 2.49/0.72    spl4_23 | spl4_24 | ~spl4_12),
% 2.49/0.72    inference(avatar_split_clause,[],[f631,f577,f685,f680])).
% 2.49/0.72  fof(f685,plain,(
% 2.49/0.72    spl4_24 <=> r2_hidden(sK3(k2_tarski(sK0,sK0),sK2),k2_tarski(sK0,sK0))),
% 2.49/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.49/0.72  fof(f631,plain,(
% 2.49/0.72    r2_hidden(sK3(k2_tarski(sK0,sK0),sK2),k2_tarski(sK0,sK0)) | r1_xboole_0(k2_tarski(sK0,sK0),sK2) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f198,f579])).
% 2.49/0.72  fof(f198,plain,(
% 2.49/0.72    ( ! [X2,X1] : (r2_hidden(sK3(X1,X2),k3_xboole_0(X2,X1)) | r1_xboole_0(X1,X2)) )),
% 2.49/0.72    inference(superposition,[],[f56,f52])).
% 2.49/0.72  fof(f683,plain,(
% 2.49/0.72    ~spl4_23 | spl4_17 | ~spl4_12),
% 2.49/0.72    inference(avatar_split_clause,[],[f630,f577,f649,f680])).
% 2.49/0.72  fof(f649,plain,(
% 2.49/0.72    spl4_17 <=> ! [X0] : ~r2_hidden(X0,k2_tarski(sK0,sK0))),
% 2.49/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.49/0.72  fof(f630,plain,(
% 2.49/0.72    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK0,sK0)) | ~r1_xboole_0(k2_tarski(sK0,sK0),sK2)) ) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f121,f579])).
% 2.49/0.72  fof(f678,plain,(
% 2.49/0.72    spl4_19 | ~spl4_12),
% 2.49/0.72    inference(avatar_split_clause,[],[f677,f577,f658])).
% 2.49/0.72  fof(f677,plain,(
% 2.49/0.72    r1_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(sK2,k2_tarski(sK0,sK0))) | ~spl4_12),
% 2.49/0.72    inference(forward_demodulation,[],[f629,f51])).
% 2.49/0.72  fof(f629,plain,(
% 2.49/0.72    r1_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK0),sK2)) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f100,f579])).
% 2.49/0.72  fof(f676,plain,(
% 2.49/0.72    spl4_22 | ~spl4_12),
% 2.49/0.72    inference(avatar_split_clause,[],[f628,f577,f673])).
% 2.49/0.72  fof(f673,plain,(
% 2.49/0.72    spl4_22 <=> r1_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),sK2)),
% 2.49/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 2.49/0.72  fof(f628,plain,(
% 2.49/0.72    r1_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),sK2) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f91,f579])).
% 2.49/0.72  fof(f671,plain,(
% 2.49/0.72    spl4_21 | ~spl4_12),
% 2.49/0.72    inference(avatar_split_clause,[],[f626,f577,f668])).
% 2.49/0.72  fof(f626,plain,(
% 2.49/0.72    r1_tarski(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),sK2) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f69,f579])).
% 2.49/0.72  fof(f69,plain,(
% 2.49/0.72    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.49/0.72    inference(definition_unfolding,[],[f46,f44])).
% 2.49/0.72  fof(f46,plain,(
% 2.49/0.72    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.49/0.72    inference(cnf_transformation,[],[f12])).
% 2.49/0.72  fof(f12,axiom,(
% 2.49/0.72    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.49/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.49/0.72  fof(f666,plain,(
% 2.49/0.72    spl4_20 | ~spl4_12),
% 2.49/0.72    inference(avatar_split_clause,[],[f625,f577,f663])).
% 2.49/0.72  fof(f625,plain,(
% 2.49/0.72    r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f68,f579])).
% 2.49/0.72  fof(f661,plain,(
% 2.49/0.72    spl4_19 | ~spl4_12),
% 2.49/0.72    inference(avatar_split_clause,[],[f624,f577,f658])).
% 2.49/0.72  fof(f624,plain,(
% 2.49/0.72    r1_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(sK2,k2_tarski(sK0,sK0))) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f57,f579])).
% 2.49/0.72  fof(f656,plain,(
% 2.49/0.72    spl4_16 | spl4_18 | ~spl4_12),
% 2.49/0.72    inference(avatar_split_clause,[],[f623,f577,f653,f645])).
% 2.49/0.72  fof(f653,plain,(
% 2.49/0.72    spl4_18 <=> r2_hidden(sK3(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))),
% 2.49/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.49/0.72  fof(f623,plain,(
% 2.49/0.72    r2_hidden(sK3(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | r1_xboole_0(sK2,k2_tarski(sK0,sK0)) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f56,f579])).
% 2.49/0.72  fof(f651,plain,(
% 2.49/0.72    ~spl4_16 | spl4_17 | ~spl4_12),
% 2.49/0.72    inference(avatar_split_clause,[],[f622,f577,f649,f645])).
% 2.49/0.72  fof(f622,plain,(
% 2.49/0.72    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK0,sK0)) | ~r1_xboole_0(sK2,k2_tarski(sK0,sK0))) ) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f55,f579])).
% 2.49/0.72  fof(f643,plain,(
% 2.49/0.72    ~spl4_15 | ~spl4_12),
% 2.49/0.72    inference(avatar_split_clause,[],[f621,f577,f639])).
% 2.49/0.72  fof(f639,plain,(
% 2.49/0.72    spl4_15 <=> r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK0)))),
% 2.49/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.49/0.72  fof(f621,plain,(
% 2.49/0.72    ~r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK0))) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f211,f579])).
% 2.49/0.72  fof(f211,plain,(
% 2.49/0.72    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X2,X0))))) )),
% 2.49/0.72    inference(resolution,[],[f202,f118])).
% 2.49/0.72  fof(f642,plain,(
% 2.49/0.72    ~spl4_15 | ~spl4_12),
% 2.49/0.72    inference(avatar_split_clause,[],[f620,f577,f639])).
% 2.49/0.72  fof(f620,plain,(
% 2.49/0.72    ~r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK0))) | ~spl4_12),
% 2.49/0.72    inference(superposition,[],[f212,f579])).
% 2.49/0.72  fof(f608,plain,(
% 2.49/0.72    ~spl4_3 | ~spl4_13),
% 2.49/0.72    inference(avatar_contradiction_clause,[],[f606])).
% 2.49/0.72  fof(f606,plain,(
% 2.49/0.72    $false | (~spl4_3 | ~spl4_13)),
% 2.49/0.72    inference(subsumption_resolution,[],[f83,f604])).
% 2.49/0.72  fof(f604,plain,(
% 2.49/0.72    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl4_13),
% 2.49/0.72    inference(resolution,[],[f585,f120])).
% 2.49/0.72  fof(f120,plain,(
% 2.49/0.72    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | ~r2_hidden(X1,X0)) )),
% 2.49/0.72    inference(superposition,[],[f55,f53])).
% 2.49/0.72  fof(f585,plain,(
% 2.49/0.72    r1_xboole_0(sK2,sK2) | ~spl4_13),
% 2.49/0.72    inference(avatar_component_clause,[],[f583])).
% 2.49/0.72  fof(f583,plain,(
% 2.49/0.72    spl4_13 <=> r1_xboole_0(sK2,sK2)),
% 2.49/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.49/0.72  fof(f83,plain,(
% 2.49/0.72    r2_hidden(sK0,sK2) | ~spl4_3),
% 2.49/0.72    inference(avatar_component_clause,[],[f82])).
% 2.49/0.72  fof(f601,plain,(
% 2.49/0.72    spl4_4 | ~spl4_1),
% 2.49/0.72    inference(avatar_split_clause,[],[f600,f73,f95])).
% 2.49/0.72  fof(f73,plain,(
% 2.49/0.72    spl4_1 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.49/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.49/0.72  fof(f600,plain,(
% 2.49/0.72    k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl4_1),
% 2.49/0.72    inference(forward_demodulation,[],[f75,f52])).
% 2.49/0.72  fof(f75,plain,(
% 2.49/0.72    k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) | ~spl4_1),
% 2.49/0.72    inference(avatar_component_clause,[],[f73])).
% 2.49/0.72  fof(f599,plain,(
% 2.49/0.72    spl4_2 | ~spl4_9),
% 2.49/0.72    inference(avatar_contradiction_clause,[],[f598])).
% 2.49/0.72  fof(f598,plain,(
% 2.49/0.72    $false | (spl4_2 | ~spl4_9)),
% 2.49/0.72    inference(subsumption_resolution,[],[f594,f79])).
% 2.49/0.72  fof(f79,plain,(
% 2.49/0.72    ~r2_hidden(sK1,sK2) | spl4_2),
% 2.49/0.72    inference(avatar_component_clause,[],[f77])).
% 2.49/0.72  fof(f594,plain,(
% 2.49/0.72    r2_hidden(sK1,sK2) | ~spl4_9),
% 2.49/0.72    inference(resolution,[],[f543,f264])).
% 2.49/0.72  fof(f264,plain,(
% 2.49/0.72    ( ! [X4,X5,X3] : (~r2_hidden(X3,k3_xboole_0(X4,k2_tarski(X5,X3))) | r2_hidden(X3,X4)) )),
% 2.49/0.72    inference(resolution,[],[f211,f42])).
% 2.49/0.72  fof(f42,plain,(
% 2.49/0.72    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.49/0.72    inference(cnf_transformation,[],[f31])).
% 2.49/0.72  fof(f592,plain,(
% 2.49/0.72    ~spl4_4 | spl4_1),
% 2.49/0.72    inference(avatar_split_clause,[],[f591,f73,f95])).
% 2.49/0.72  fof(f591,plain,(
% 2.49/0.72    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl4_1),
% 2.49/0.72    inference(forward_demodulation,[],[f74,f52])).
% 2.49/0.72  fof(f74,plain,(
% 2.49/0.72    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl4_1),
% 2.49/0.72    inference(avatar_component_clause,[],[f73])).
% 2.49/0.72  fof(f590,plain,(
% 2.49/0.72    spl4_13 | spl4_14 | ~spl4_3),
% 2.49/0.72    inference(avatar_split_clause,[],[f581,f82,f587,f583])).
% 2.49/0.72  fof(f587,plain,(
% 2.49/0.72    spl4_14 <=> k2_tarski(sK0,sK3(sK2,sK2)) = k3_xboole_0(sK2,k2_tarski(sK0,sK3(sK2,sK2)))),
% 2.49/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.49/0.72  fof(f581,plain,(
% 2.49/0.72    k2_tarski(sK0,sK3(sK2,sK2)) = k3_xboole_0(sK2,k2_tarski(sK0,sK3(sK2,sK2))) | r1_xboole_0(sK2,sK2) | ~spl4_3),
% 2.49/0.72    inference(forward_demodulation,[],[f575,f48])).
% 2.49/0.72  fof(f575,plain,(
% 2.49/0.72    k2_tarski(sK3(sK2,sK2),sK0) = k3_xboole_0(sK2,k2_tarski(sK3(sK2,sK2),sK0)) | r1_xboole_0(sK2,sK2) | ~spl4_3),
% 2.49/0.72    inference(resolution,[],[f567,f197])).
% 2.49/0.72  fof(f567,plain,(
% 2.49/0.72    ( ! [X0] : (~r2_hidden(X0,sK2) | k2_tarski(X0,sK0) = k3_xboole_0(sK2,k2_tarski(X0,sK0))) ) | ~spl4_3),
% 2.49/0.72    inference(forward_demodulation,[],[f566,f52])).
% 2.49/0.72  fof(f566,plain,(
% 2.49/0.72    ( ! [X0] : (~r2_hidden(X0,sK2) | k2_tarski(X0,sK0) = k3_xboole_0(k2_tarski(X0,sK0),sK2)) ) | ~spl4_3),
% 2.49/0.72    inference(resolution,[],[f83,f47])).
% 2.49/0.72  fof(f47,plain,(
% 2.49/0.72    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1) | k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 2.49/0.72    inference(cnf_transformation,[],[f33])).
% 2.49/0.72  fof(f33,plain,(
% 2.49/0.72    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 2.49/0.72    inference(flattening,[],[f32])).
% 2.49/0.72  fof(f32,plain,(
% 2.49/0.72    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 2.49/0.72    inference(ennf_transformation,[],[f24])).
% 2.49/0.72  fof(f24,axiom,(
% 2.49/0.72    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 2.49/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 2.49/0.72  fof(f580,plain,(
% 2.49/0.72    spl4_12 | ~spl4_3),
% 2.49/0.72    inference(avatar_split_clause,[],[f574,f82,f577])).
% 2.49/0.72  fof(f574,plain,(
% 2.49/0.72    k2_tarski(sK0,sK0) = k3_xboole_0(sK2,k2_tarski(sK0,sK0)) | ~spl4_3),
% 2.49/0.72    inference(resolution,[],[f567,f83])).
% 2.49/0.72  fof(f565,plain,(
% 2.49/0.72    ~spl4_11 | ~spl4_8),
% 2.49/0.72    inference(avatar_split_clause,[],[f547,f529,f562])).
% 2.49/0.72  fof(f547,plain,(
% 2.49/0.72    ~r1_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~spl4_8),
% 2.49/0.72    inference(resolution,[],[f531,f55])).
% 2.49/0.72  fof(f531,plain,(
% 2.49/0.72    r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl4_8),
% 2.49/0.72    inference(avatar_component_clause,[],[f529])).
% 2.49/0.72  fof(f560,plain,(
% 2.49/0.72    ~spl4_10 | ~spl4_8),
% 2.49/0.72    inference(avatar_split_clause,[],[f546,f529,f557])).
% 2.49/0.72  fof(f546,plain,(
% 2.49/0.72    ~r1_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl4_8),
% 2.49/0.72    inference(resolution,[],[f531,f121])).
% 2.49/0.72  fof(f555,plain,(
% 2.49/0.72    spl4_4 | ~spl4_1),
% 2.49/0.72    inference(avatar_split_clause,[],[f552,f73,f95])).
% 2.49/0.72  fof(f552,plain,(
% 2.49/0.72    k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl4_1),
% 2.49/0.72    inference(forward_demodulation,[],[f75,f52])).
% 2.49/0.72  fof(f554,plain,(
% 2.49/0.72    ~spl4_1 | spl4_4),
% 2.49/0.72    inference(avatar_contradiction_clause,[],[f553])).
% 2.49/0.72  fof(f553,plain,(
% 2.49/0.72    $false | (~spl4_1 | spl4_4)),
% 2.49/0.72    inference(subsumption_resolution,[],[f552,f97])).
% 2.49/0.72  fof(f97,plain,(
% 2.49/0.72    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl4_4),
% 2.49/0.72    inference(avatar_component_clause,[],[f95])).
% 2.49/0.72  fof(f551,plain,(
% 2.49/0.72    spl4_3 | ~spl4_8),
% 2.49/0.72    inference(avatar_split_clause,[],[f545,f529,f82])).
% 2.49/0.72  fof(f545,plain,(
% 2.49/0.72    r2_hidden(sK0,sK2) | ~spl4_8),
% 2.49/0.72    inference(resolution,[],[f531,f272])).
% 2.49/0.72  fof(f272,plain,(
% 2.49/0.72    ( ! [X4,X5,X3] : (~r2_hidden(X3,k3_xboole_0(X4,k2_tarski(X3,X5))) | r2_hidden(X3,X4)) )),
% 2.49/0.72    inference(resolution,[],[f212,f42])).
% 2.49/0.72  fof(f550,plain,(
% 2.49/0.72    spl4_3 | ~spl4_8),
% 2.49/0.72    inference(avatar_contradiction_clause,[],[f549])).
% 2.49/0.72  fof(f549,plain,(
% 2.49/0.72    $false | (spl4_3 | ~spl4_8)),
% 2.49/0.72    inference(subsumption_resolution,[],[f545,f84])).
% 2.49/0.72  fof(f84,plain,(
% 2.49/0.72    ~r2_hidden(sK0,sK2) | spl4_3),
% 2.49/0.72    inference(avatar_component_clause,[],[f82])).
% 2.49/0.72  fof(f544,plain,(
% 2.49/0.72    spl4_9 | spl4_7),
% 2.49/0.72    inference(avatar_split_clause,[],[f539,f521,f541])).
% 2.49/0.72  fof(f521,plain,(
% 2.49/0.72    spl4_7 <=> r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))),
% 2.49/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.49/0.72  fof(f539,plain,(
% 2.49/0.72    r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl4_7),
% 2.49/0.72    inference(subsumption_resolution,[],[f537,f126])).
% 2.49/0.72  fof(f126,plain,(
% 2.49/0.72    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 2.49/0.72    inference(superposition,[],[f123,f48])).
% 2.49/0.72  fof(f123,plain,(
% 2.49/0.72    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 2.49/0.72    inference(resolution,[],[f58,f70])).
% 2.49/0.72  fof(f58,plain,(
% 2.49/0.72    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 2.49/0.72    inference(cnf_transformation,[],[f23])).
% 2.49/0.72  fof(f23,axiom,(
% 2.49/0.72    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.49/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.49/0.72  fof(f537,plain,(
% 2.49/0.72    ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl4_7),
% 2.49/0.72    inference(resolution,[],[f523,f43])).
% 2.49/0.72  fof(f523,plain,(
% 2.49/0.72    ~r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | spl4_7),
% 2.49/0.72    inference(avatar_component_clause,[],[f521])).
% 2.49/0.72  fof(f532,plain,(
% 2.49/0.72    spl4_8 | spl4_6),
% 2.49/0.72    inference(avatar_split_clause,[],[f527,f517,f529])).
% 2.49/0.72  fof(f517,plain,(
% 2.49/0.72    spl4_6 <=> r2_hidden(sK0,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))),
% 2.49/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.49/0.72  fof(f527,plain,(
% 2.49/0.72    r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl4_6),
% 2.49/0.72    inference(subsumption_resolution,[],[f525,f123])).
% 2.49/0.72  fof(f525,plain,(
% 2.49/0.72    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl4_6),
% 2.49/0.72    inference(resolution,[],[f519,f43])).
% 2.49/0.72  fof(f519,plain,(
% 2.49/0.72    ~r2_hidden(sK0,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | spl4_6),
% 2.49/0.72    inference(avatar_component_clause,[],[f517])).
% 2.49/0.72  fof(f524,plain,(
% 2.49/0.72    ~spl4_6 | ~spl4_7 | spl4_5),
% 2.49/0.72    inference(avatar_split_clause,[],[f510,f153,f521,f517])).
% 2.49/0.72  fof(f510,plain,(
% 2.49/0.72    ~r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | ~r2_hidden(sK0,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | spl4_5),
% 2.49/0.72    inference(resolution,[],[f60,f155])).
% 2.49/0.72  fof(f60,plain,(
% 2.49/0.72    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.49/0.72    inference(cnf_transformation,[],[f23])).
% 2.49/0.72  fof(f158,plain,(
% 2.49/0.72    ~spl4_5 | spl4_4),
% 2.49/0.72    inference(avatar_split_clause,[],[f157,f95,f153])).
% 2.49/0.72  fof(f157,plain,(
% 2.49/0.72    ~r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | spl4_4),
% 2.49/0.72    inference(subsumption_resolution,[],[f146,f90])).
% 2.49/0.72  fof(f90,plain,(
% 2.49/0.72    ( ! [X2,X1] : (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)) )),
% 2.49/0.72    inference(superposition,[],[f69,f52])).
% 2.49/0.72  fof(f146,plain,(
% 2.49/0.72    ~r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | ~r1_tarski(k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1)) | spl4_4),
% 2.49/0.72    inference(extensionality_resolution,[],[f63,f97])).
% 2.49/0.72  fof(f156,plain,(
% 2.49/0.72    ~spl4_5 | spl4_4),
% 2.49/0.72    inference(avatar_split_clause,[],[f151,f95,f153])).
% 2.49/0.72  fof(f151,plain,(
% 2.49/0.72    ~r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | spl4_4),
% 2.49/0.72    inference(subsumption_resolution,[],[f145,f90])).
% 2.49/0.72  fof(f145,plain,(
% 2.49/0.72    ~r1_tarski(k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1)) | ~r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | spl4_4),
% 2.49/0.72    inference(extensionality_resolution,[],[f63,f97])).
% 2.49/0.72  fof(f98,plain,(
% 2.49/0.72    ~spl4_4 | spl4_1),
% 2.49/0.72    inference(avatar_split_clause,[],[f89,f73,f95])).
% 2.49/0.72  fof(f89,plain,(
% 2.49/0.72    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl4_1),
% 2.49/0.72    inference(backward_demodulation,[],[f74,f52])).
% 2.49/0.72  fof(f86,plain,(
% 2.49/0.72    ~spl4_1 | spl4_2 | spl4_3),
% 2.49/0.72    inference(avatar_split_clause,[],[f67,f82,f77,f73])).
% 2.49/0.72  fof(f67,plain,(
% 2.49/0.72    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.49/0.72    inference(definition_unfolding,[],[f37,f44])).
% 2.49/0.72  fof(f37,plain,(
% 2.49/0.72    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.49/0.72    inference(cnf_transformation,[],[f30])).
% 2.49/0.72  fof(f30,plain,(
% 2.49/0.72    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.49/0.72    inference(ennf_transformation,[],[f27])).
% 2.49/0.72  fof(f27,negated_conjecture,(
% 2.49/0.72    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.49/0.72    inference(negated_conjecture,[],[f26])).
% 2.49/0.72  fof(f26,conjecture,(
% 2.49/0.72    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.49/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 2.49/0.72  fof(f85,plain,(
% 2.49/0.72    spl4_1 | ~spl4_3),
% 2.49/0.72    inference(avatar_split_clause,[],[f66,f82,f73])).
% 2.49/0.72  fof(f66,plain,(
% 2.49/0.72    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.49/0.72    inference(definition_unfolding,[],[f38,f44])).
% 2.49/0.72  fof(f38,plain,(
% 2.49/0.72    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.49/0.72    inference(cnf_transformation,[],[f30])).
% 2.49/0.72  fof(f80,plain,(
% 2.49/0.72    spl4_1 | ~spl4_2),
% 2.49/0.72    inference(avatar_split_clause,[],[f65,f77,f73])).
% 2.49/0.72  fof(f65,plain,(
% 2.49/0.72    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.49/0.72    inference(definition_unfolding,[],[f39,f44])).
% 2.49/0.72  fof(f39,plain,(
% 2.49/0.72    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.49/0.72    inference(cnf_transformation,[],[f30])).
% 2.49/0.72  % SZS output end Proof for theBenchmark
% 2.49/0.72  % (6306)------------------------------
% 2.49/0.72  % (6306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.49/0.72  % (6306)Termination reason: Refutation
% 2.49/0.72  
% 2.49/0.72  % (6306)Memory used [KB]: 2046
% 2.49/0.72  % (6306)Time elapsed: 0.334 s
% 2.49/0.72  % (6306)------------------------------
% 2.49/0.72  % (6306)------------------------------
% 2.49/0.72  % (6298)Success in time 0.378 s
%------------------------------------------------------------------------------
