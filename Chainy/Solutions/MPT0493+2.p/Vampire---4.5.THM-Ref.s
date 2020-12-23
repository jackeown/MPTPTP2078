%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0493+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:33 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 101 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  123 ( 262 expanded)
%              Number of equality atoms :   38 (  85 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1840,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1799,f1803,f1807,f1816,f1823,f1835,f1837,f1839])).

fof(f1839,plain,(
    spl68_6 ),
    inference(avatar_contradiction_clause,[],[f1838])).

fof(f1838,plain,
    ( $false
    | spl68_6 ),
    inference(global_subsumption,[],[f1182,f1828])).

fof(f1828,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | spl68_6 ),
    inference(trivial_inequality_removal,[],[f1826])).

fof(f1826,plain,
    ( sK0 != sK0
    | ~ r1_tarski(sK0,k1_relat_1(sK1))
    | spl68_6 ),
    inference(superposition,[],[f1822,f1280])).

fof(f1280,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f801])).

fof(f801,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1822,plain,
    ( sK0 != k3_xboole_0(sK0,k1_relat_1(sK1))
    | spl68_6 ),
    inference(avatar_component_clause,[],[f1821])).

fof(f1821,plain,
    ( spl68_6
  <=> sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_6])])).

fof(f1182,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f986])).

fof(f986,plain,
    ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f743,f985])).

fof(f985,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f743,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f742])).

fof(f742,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f736])).

fof(f736,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f735])).

fof(f735,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f1837,plain,(
    spl68_6 ),
    inference(avatar_contradiction_clause,[],[f1836])).

fof(f1836,plain,
    ( $false
    | spl68_6 ),
    inference(global_subsumption,[],[f1182,f1828])).

fof(f1835,plain,
    ( ~ spl68_7
    | ~ spl68_8
    | spl68_6 ),
    inference(avatar_split_clause,[],[f1825,f1821,f1833,f1830])).

fof(f1830,plain,
    ( spl68_7
  <=> r1_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_7])])).

fof(f1833,plain,
    ( spl68_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_8])])).

fof(f1825,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_xboole_0(sK0,k1_relat_1(sK1))
    | spl68_6 ),
    inference(superposition,[],[f1822,f1505])).

fof(f1505,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1129])).

fof(f1129,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1823,plain,
    ( ~ spl68_6
    | spl68_1 ),
    inference(avatar_split_clause,[],[f1819,f1797,f1821])).

fof(f1797,plain,
    ( spl68_1
  <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_1])])).

fof(f1819,plain,
    ( sK0 != k3_xboole_0(sK0,k1_relat_1(sK1))
    | spl68_1 ),
    inference(global_subsumption,[],[f1181,f1818])).

fof(f1818,plain,
    ( sK0 != k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl68_1 ),
    inference(forward_demodulation,[],[f1817,f1286])).

fof(f1286,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1817,plain,
    ( sK0 != k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | spl68_1 ),
    inference(superposition,[],[f1798,f1189])).

fof(f1189,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f747])).

fof(f747,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f734])).

fof(f734,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f1798,plain,
    ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
    | spl68_1 ),
    inference(avatar_component_clause,[],[f1797])).

fof(f1181,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f986])).

fof(f1816,plain,
    ( ~ spl68_4
    | spl68_5
    | ~ spl68_2 ),
    inference(avatar_split_clause,[],[f1809,f1801,f1814,f1811])).

fof(f1811,plain,
    ( spl68_4
  <=> r1_tarski(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_4])])).

fof(f1814,plain,
    ( spl68_5
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_5])])).

fof(f1801,plain,
    ( spl68_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_2])])).

fof(f1809,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ r1_tarski(k1_relat_1(sK1),sK0)
    | ~ spl68_2 ),
    inference(resolution,[],[f1802,f1203])).

fof(f1203,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f995])).

fof(f995,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f994])).

fof(f994,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1802,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl68_2 ),
    inference(avatar_component_clause,[],[f1801])).

fof(f1807,plain,(
    spl68_3 ),
    inference(avatar_split_clause,[],[f1181,f1805])).

fof(f1805,plain,
    ( spl68_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_3])])).

fof(f1803,plain,(
    spl68_2 ),
    inference(avatar_split_clause,[],[f1182,f1801])).

fof(f1799,plain,(
    ~ spl68_1 ),
    inference(avatar_split_clause,[],[f1183,f1797])).

fof(f1183,plain,(
    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f986])).
%------------------------------------------------------------------------------
