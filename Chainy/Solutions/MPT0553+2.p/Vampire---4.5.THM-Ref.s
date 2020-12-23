%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0553+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:36 EST 2020

% Result     : Theorem 8.12s
% Output     : Refutation 8.12s
% Verified   : 
% Statistics : Number of formulae       :   38 (  53 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 (  97 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9516,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2265,f2275,f9509])).

fof(f9509,plain,
    ( ~ spl103_1
    | spl103_3 ),
    inference(avatar_contradiction_clause,[],[f9508])).

fof(f9508,plain,
    ( $false
    | ~ spl103_1
    | spl103_3 ),
    inference(subsumption_resolution,[],[f9507,f4146])).

fof(f4146,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k2_xboole_0(X0,X1)))
    | ~ spl103_1 ),
    inference(superposition,[],[f1807,f2334])).

fof(f2334,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
    | ~ spl103_1 ),
    inference(unit_resulting_resolution,[],[f2264,f1431])).

fof(f1431,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f822])).

fof(f822,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f735])).

fof(f735,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

fof(f2264,plain,
    ( v1_relat_1(sK2)
    | ~ spl103_1 ),
    inference(avatar_component_clause,[],[f2262])).

fof(f2262,plain,
    ( spl103_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_1])])).

fof(f1807,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f9507,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | ~ spl103_1
    | spl103_3 ),
    inference(forward_demodulation,[],[f9506,f1806])).

fof(f1806,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f9506,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,sK0)))
    | ~ spl103_1
    | spl103_3 ),
    inference(forward_demodulation,[],[f9505,f1579])).

fof(f1579,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f9505,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))))
    | ~ spl103_1
    | spl103_3 ),
    inference(forward_demodulation,[],[f9496,f2334])).

fof(f9496,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,k4_xboole_0(sK0,sK1))))
    | spl103_3 ),
    inference(unit_resulting_resolution,[],[f2274,f1534])).

fof(f1534,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f909])).

fof(f909,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f105])).

fof(f105,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f2274,plain,
    ( ~ r1_tarski(k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k4_xboole_0(sK0,sK1)))
    | spl103_3 ),
    inference(avatar_component_clause,[],[f2272])).

fof(f2272,plain,
    ( spl103_3
  <=> r1_tarski(k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_3])])).

fof(f2275,plain,(
    ~ spl103_3 ),
    inference(avatar_split_clause,[],[f2221,f2272])).

fof(f2221,plain,(
    ~ r1_tarski(k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2218,f1421])).

fof(f1421,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f2218,plain,(
    ~ r1_tarski(k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f1414,f1421])).

fof(f1414,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f1182])).

fof(f1182,plain,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f812,f1181])).

fof(f1181,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f812,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f738])).

fof(f738,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(negated_conjecture,[],[f737])).

fof(f737,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).

fof(f2265,plain,(
    spl103_1 ),
    inference(avatar_split_clause,[],[f1413,f2262])).

fof(f1413,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1182])).
%------------------------------------------------------------------------------
