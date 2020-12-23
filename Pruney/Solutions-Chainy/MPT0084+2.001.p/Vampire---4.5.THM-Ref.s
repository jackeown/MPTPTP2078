%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 298 expanded)
%              Number of leaves         :   37 ( 127 expanded)
%              Depth                    :    9
%              Number of atoms          :  323 ( 626 expanded)
%              Number of equality atoms :   73 ( 197 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2422,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f65,f71,f158,f183,f189,f202,f314,f332,f1119,f1587,f1715,f1730,f1976,f2026,f2028,f2399,f2405,f2418,f2419,f2421])).

fof(f2421,plain,
    ( spl4_3
    | ~ spl4_65 ),
    inference(avatar_split_clause,[],[f2420,f2015,f56])).

fof(f56,plain,
    ( spl4_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f2015,plain,
    ( spl4_65
  <=> ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f2420,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_65 ),
    inference(resolution,[],[f2016,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f2016,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f2015])).

fof(f2419,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1))
    | k1_xboole_0 != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2418,plain,
    ( spl4_75
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f2409,f2402,f2412])).

fof(f2412,plain,
    ( spl4_75
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f2402,plain,
    ( spl4_74
  <=> k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f2409,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1))
    | ~ spl4_74 ),
    inference(superposition,[],[f33,f2404])).

fof(f2404,plain,
    ( k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f2402])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2405,plain,
    ( spl4_74
    | ~ spl4_73 ),
    inference(avatar_split_clause,[],[f2400,f2396,f2402])).

fof(f2396,plain,
    ( spl4_73
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f2400,plain,
    ( k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl4_73 ),
    inference(resolution,[],[f2398,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f2398,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f2396])).

fof(f2399,plain,
    ( ~ spl4_53
    | spl4_73
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f2394,f1727,f2396,f1116])).

fof(f1116,plain,
    ( spl4_53
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f1727,plain,
    ( spl4_58
  <=> k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f2394,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl4_58 ),
    inference(resolution,[],[f1756,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1756,plain,
    ( ! [X5] :
        ( ~ r1_tarski(X5,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
        | r1_tarski(X5,k1_xboole_0)
        | ~ r1_tarski(X5,sK0) )
    | ~ spl4_58 ),
    inference(superposition,[],[f44,f1729])).

fof(f1729,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f1727])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f2028,plain,
    ( ~ spl4_66
    | spl4_64
    | ~ spl4_5
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f2027,f1973,f68,f2011,f2019])).

fof(f2019,plain,
    ( spl4_66
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f2011,plain,
    ( spl4_64
  <=> r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f68,plain,
    ( spl4_5
  <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1973,plain,
    ( spl4_62
  <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f2027,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK2))))
    | k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | ~ spl4_5
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f1995,f33])).

fof(f1995,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,k2_xboole_0(sK2,sK2)),k3_xboole_0(sK1,sK2)))
    | ~ spl4_5
    | ~ spl4_62 ),
    inference(superposition,[],[f249,f1975])).

fof(f1975,plain,
    ( k3_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(sK2,sK2))))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f1973])).

fof(f249,plain,
    ( ! [X9] :
        ( k1_xboole_0 != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X9))
        | r1_xboole_0(sK0,k2_xboole_0(X9,k3_xboole_0(sK1,sK2))) )
    | ~ spl4_5 ),
    inference(superposition,[],[f42,f96])).

fof(f96,plain,
    ( ! [X2] : k3_xboole_0(sK0,k2_xboole_0(X2,k3_xboole_0(sK1,sK2))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f79,f33])).

fof(f79,plain,
    ( ! [X2] : k3_xboole_0(sK0,k2_xboole_0(X2,k3_xboole_0(sK1,sK2))) = k2_xboole_0(k3_xboole_0(sK0,X2),k1_xboole_0)
    | ~ spl4_5 ),
    inference(superposition,[],[f43,f70])).

fof(f70,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f2026,plain,
    ( spl4_65
    | ~ spl4_64
    | ~ spl4_5
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f2025,f1973,f68,f2011,f2015])).

fof(f2025,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK2))))
        | ~ r2_hidden(X1,k3_xboole_0(sK0,sK1)) )
    | ~ spl4_5
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f1994,f33])).

fof(f1994,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_xboole_0(sK0,sK1))
        | ~ r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,k2_xboole_0(sK2,sK2)),k3_xboole_0(sK1,sK2))) )
    | ~ spl4_5
    | ~ spl4_62 ),
    inference(superposition,[],[f248,f1975])).

fof(f248,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(X8,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X7)))
        | ~ r1_xboole_0(sK0,k2_xboole_0(X7,k3_xboole_0(sK1,sK2))) )
    | ~ spl4_5 ),
    inference(superposition,[],[f39,f96])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1976,plain,
    ( spl4_62
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f1940,f329,f1973])).

fof(f329,plain,
    ( spl4_23
  <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f1940,plain,
    ( k3_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(sK2,sK2))))
    | ~ spl4_23 ),
    inference(superposition,[],[f349,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f349,plain,
    ( ! [X2] : k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)) = k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,k2_xboole_0(sK2,sK2)),X2))
    | ~ spl4_23 ),
    inference(superposition,[],[f43,f331])).

fof(f331,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK2,sK2)))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f329])).

fof(f1730,plain,
    ( spl4_58
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f1725,f1707,f1727])).

fof(f1707,plain,
    ( spl4_57
  <=> r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f1725,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
    | ~ spl4_57 ),
    inference(resolution,[],[f1709,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1709,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f1707])).

fof(f1715,plain,
    ( spl4_57
    | ~ spl4_5
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f1697,f1584,f68,f1707])).

fof(f1584,plain,
    ( spl4_55
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f1697,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
    | ~ spl4_5
    | ~ spl4_55 ),
    inference(trivial_inequality_removal,[],[f1688])).

fof(f1688,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
    | ~ spl4_5
    | ~ spl4_55 ),
    inference(superposition,[],[f249,f1586])).

fof(f1586,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f1584])).

fof(f1587,plain,
    ( spl4_55
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f1582,f68,f62,f1584])).

fof(f62,plain,
    ( spl4_4
  <=> sK2 = k2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1582,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1581,f70])).

fof(f1581,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1555,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1555,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(sK1,sK0)))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(superposition,[],[f242,f64])).

fof(f64,plain,
    ( sK2 = k2_xboole_0(sK0,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f242,plain,
    ( ! [X2] : k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(sK1,X2))) = k3_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(X2,sK2)))
    | ~ spl4_5 ),
    inference(superposition,[],[f96,f43])).

fof(f1119,plain,
    ( spl4_53
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f1097,f155,f68,f1116])).

fof(f155,plain,
    ( spl4_15
  <=> k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1097,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(superposition,[],[f1029,f157])).

fof(f157,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f155])).

fof(f1029,plain,
    ( ! [X2] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)),sK0)
    | ~ spl4_5 ),
    inference(superposition,[],[f32,f147])).

fof(f147,plain,
    ( ! [X3] : sK0 = k2_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X3)),k4_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X3)))
    | ~ spl4_5 ),
    inference(superposition,[],[f37,f78])).

fof(f78,plain,
    ( ! [X1] : k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X1))
    | ~ spl4_5 ),
    inference(superposition,[],[f43,f70])).

fof(f332,plain,
    ( spl4_23
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f327,f311,f329])).

fof(f311,plain,
    ( spl4_21
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f327,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK2,sK2)))
    | ~ spl4_21 ),
    inference(resolution,[],[f313,f41])).

fof(f313,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK2,sK2)))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f311])).

fof(f314,plain,
    ( spl4_21
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f309,f199,f68,f311])).

fof(f199,plain,
    ( spl4_19
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f309,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK2,sK2)))
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f308,f43])).

fof(f308,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(trivial_inequality_removal,[],[f307])).

fof(f307,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f295,f201])).

fof(f201,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f199])).

fof(f295,plain,
    ( k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | ~ spl4_5 ),
    inference(superposition,[],[f150,f70])).

fof(f150,plain,
    ( ! [X7] :
        ( k1_xboole_0 != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X7))
        | r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X7)) )
    | ~ spl4_5 ),
    inference(superposition,[],[f42,f78])).

fof(f202,plain,
    ( spl4_19
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f197,f68,f199])).

fof(f197,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f192,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f192,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k1_xboole_0))
    | ~ spl4_5 ),
    inference(superposition,[],[f159,f31])).

fof(f159,plain,
    ( ! [X3] : k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK1,sK2),X3)))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f145,f70])).

fof(f145,plain,
    ( ! [X3] : k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK1,sK2),X3)))
    | ~ spl4_5 ),
    inference(superposition,[],[f78,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f189,plain,
    ( spl4_18
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f184,f180,f186])).

fof(f186,plain,
    ( spl4_18
  <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f180,plain,
    ( spl4_17
  <=> r1_tarski(k1_xboole_0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f184,plain,
    ( k3_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1))
    | ~ spl4_17 ),
    inference(resolution,[],[f182,f40])).

fof(f182,plain,
    ( r1_tarski(k1_xboole_0,k3_xboole_0(sK0,sK1))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f180])).

fof(f183,plain,
    ( spl4_17
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f178,f155,f180])).

fof(f178,plain,
    ( r1_tarski(k1_xboole_0,k3_xboole_0(sK0,sK1))
    | ~ spl4_15 ),
    inference(superposition,[],[f32,f157])).

fof(f158,plain,
    ( spl4_15
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f141,f68,f155])).

fof(f141,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,sK1)
    | ~ spl4_5 ),
    inference(superposition,[],[f78,f37])).

fof(f71,plain,
    ( spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f66,f46,f68])).

fof(f46,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f66,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f48,f41])).

fof(f48,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f65,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f60,f51,f62])).

fof(f51,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f60,plain,
    ( sK2 = k2_xboole_0(sK0,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f53,f40])).

fof(f53,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f59,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f27,f56])).

fof(f27,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f54,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f28,f51])).

fof(f28,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f29,f46])).

fof(f29,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:22:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.47  % (20895)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (20903)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (20893)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (20890)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (20894)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (20891)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (20892)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (20898)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (20901)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (20902)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (20900)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (20899)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.55  % (20888)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.55  % (20905)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.55  % (20897)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.55  % (20904)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.56  % (20889)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.56  % (20896)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.59  % (20899)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.60  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f2422,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(avatar_sat_refutation,[],[f49,f54,f59,f65,f71,f158,f183,f189,f202,f314,f332,f1119,f1587,f1715,f1730,f1976,f2026,f2028,f2399,f2405,f2418,f2419,f2421])).
% 0.21/0.60  fof(f2421,plain,(
% 0.21/0.60    spl4_3 | ~spl4_65),
% 0.21/0.60    inference(avatar_split_clause,[],[f2420,f2015,f56])).
% 0.21/0.60  fof(f56,plain,(
% 0.21/0.60    spl4_3 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.60  fof(f2015,plain,(
% 0.21/0.60    spl4_65 <=> ! [X0] : ~r2_hidden(X0,k3_xboole_0(sK0,sK1))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 0.21/0.60  fof(f2420,plain,(
% 0.21/0.60    r1_xboole_0(sK0,sK1) | ~spl4_65),
% 0.21/0.60    inference(resolution,[],[f2016,f38])).
% 0.21/0.60  fof(f38,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f25])).
% 0.21/0.60  fof(f25,plain,(
% 0.21/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f24])).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f18,plain,(
% 0.21/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.60    inference(ennf_transformation,[],[f16])).
% 0.21/0.60  fof(f16,plain,(
% 0.21/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.60    inference(rectify,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.60  fof(f2016,plain,(
% 0.21/0.60    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1))) ) | ~spl4_65),
% 0.21/0.60    inference(avatar_component_clause,[],[f2015])).
% 0.21/0.60  fof(f2419,plain,(
% 0.21/0.60    k3_xboole_0(sK0,sK1) != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) | k1_xboole_0 != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.60    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.60  fof(f2418,plain,(
% 0.21/0.60    spl4_75 | ~spl4_74),
% 0.21/0.60    inference(avatar_split_clause,[],[f2409,f2402,f2412])).
% 0.21/0.60  fof(f2412,plain,(
% 0.21/0.60    spl4_75 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 0.21/0.60  fof(f2402,plain,(
% 0.21/0.60    spl4_74 <=> k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 0.21/0.60  fof(f2409,plain,(
% 0.21/0.60    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) | ~spl4_74),
% 0.21/0.60    inference(superposition,[],[f33,f2404])).
% 0.21/0.60  fof(f2404,plain,(
% 0.21/0.60    k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) | ~spl4_74),
% 0.21/0.60    inference(avatar_component_clause,[],[f2402])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f1])).
% 0.21/0.60  fof(f1,axiom,(
% 0.21/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.60  fof(f2405,plain,(
% 0.21/0.60    spl4_74 | ~spl4_73),
% 0.21/0.60    inference(avatar_split_clause,[],[f2400,f2396,f2402])).
% 0.21/0.60  fof(f2396,plain,(
% 0.21/0.60    spl4_73 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 0.21/0.60  fof(f2400,plain,(
% 0.21/0.60    k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) | ~spl4_73),
% 0.21/0.60    inference(resolution,[],[f2398,f40])).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f19])).
% 0.21/0.60  fof(f19,plain,(
% 0.21/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f5])).
% 0.21/0.60  fof(f5,axiom,(
% 0.21/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.60  fof(f2398,plain,(
% 0.21/0.60    r1_tarski(k3_xboole_0(sK0,sK1),k1_xboole_0) | ~spl4_73),
% 0.21/0.60    inference(avatar_component_clause,[],[f2396])).
% 0.21/0.60  fof(f2399,plain,(
% 0.21/0.60    ~spl4_53 | spl4_73 | ~spl4_58),
% 0.21/0.60    inference(avatar_split_clause,[],[f2394,f1727,f2396,f1116])).
% 0.21/0.60  fof(f1116,plain,(
% 0.21/0.60    spl4_53 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.21/0.60  fof(f1727,plain,(
% 0.21/0.60    spl4_58 <=> k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 0.21/0.60  fof(f2394,plain,(
% 0.21/0.60    r1_tarski(k3_xboole_0(sK0,sK1),k1_xboole_0) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | ~spl4_58),
% 0.21/0.60    inference(resolution,[],[f1756,f32])).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f13])).
% 0.21/0.60  fof(f13,axiom,(
% 0.21/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.60  fof(f1756,plain,(
% 0.21/0.60    ( ! [X5] : (~r1_tarski(X5,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) | r1_tarski(X5,k1_xboole_0) | ~r1_tarski(X5,sK0)) ) | ~spl4_58),
% 0.21/0.60    inference(superposition,[],[f44,f1729])).
% 0.21/0.60  fof(f1729,plain,(
% 0.21/0.60    k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) | ~spl4_58),
% 0.21/0.60    inference(avatar_component_clause,[],[f1727])).
% 0.21/0.60  fof(f44,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f21])).
% 0.21/0.60  fof(f21,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.60    inference(flattening,[],[f20])).
% 0.21/0.60  fof(f20,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.60    inference(ennf_transformation,[],[f6])).
% 0.21/0.60  fof(f6,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.60  fof(f2028,plain,(
% 0.21/0.60    ~spl4_66 | spl4_64 | ~spl4_5 | ~spl4_62),
% 0.21/0.60    inference(avatar_split_clause,[],[f2027,f1973,f68,f2011,f2019])).
% 0.21/0.60  fof(f2019,plain,(
% 0.21/0.60    spl4_66 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 0.21/0.60  fof(f2011,plain,(
% 0.21/0.60    spl4_64 <=> r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK2))))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 0.21/0.60  fof(f68,plain,(
% 0.21/0.60    spl4_5 <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.60  fof(f1973,plain,(
% 0.21/0.60    spl4_62 <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(sK2,sK2))))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 0.21/0.60  fof(f2027,plain,(
% 0.21/0.60    r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK2)))) | k1_xboole_0 != k3_xboole_0(sK0,sK1) | (~spl4_5 | ~spl4_62)),
% 0.21/0.60    inference(forward_demodulation,[],[f1995,f33])).
% 0.21/0.60  fof(f1995,plain,(
% 0.21/0.60    k1_xboole_0 != k3_xboole_0(sK0,sK1) | r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,k2_xboole_0(sK2,sK2)),k3_xboole_0(sK1,sK2))) | (~spl4_5 | ~spl4_62)),
% 0.21/0.60    inference(superposition,[],[f249,f1975])).
% 0.21/0.60  fof(f1975,plain,(
% 0.21/0.60    k3_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(sK2,sK2)))) | ~spl4_62),
% 0.21/0.60    inference(avatar_component_clause,[],[f1973])).
% 0.21/0.60  fof(f249,plain,(
% 0.21/0.60    ( ! [X9] : (k1_xboole_0 != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X9)) | r1_xboole_0(sK0,k2_xboole_0(X9,k3_xboole_0(sK1,sK2)))) ) | ~spl4_5),
% 0.21/0.60    inference(superposition,[],[f42,f96])).
% 0.21/0.60  fof(f96,plain,(
% 0.21/0.60    ( ! [X2] : (k3_xboole_0(sK0,k2_xboole_0(X2,k3_xboole_0(sK1,sK2))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2))) ) | ~spl4_5),
% 0.21/0.60    inference(forward_demodulation,[],[f79,f33])).
% 0.21/0.60  fof(f79,plain,(
% 0.21/0.60    ( ! [X2] : (k3_xboole_0(sK0,k2_xboole_0(X2,k3_xboole_0(sK1,sK2))) = k2_xboole_0(k3_xboole_0(sK0,X2),k1_xboole_0)) ) | ~spl4_5),
% 0.21/0.60    inference(superposition,[],[f43,f70])).
% 0.21/0.60  fof(f70,plain,(
% 0.21/0.60    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl4_5),
% 0.21/0.60    inference(avatar_component_clause,[],[f68])).
% 0.21/0.60  fof(f43,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f8])).
% 0.21/0.60  fof(f8,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.21/0.60  fof(f42,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f26])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.60    inference(nnf_transformation,[],[f3])).
% 0.21/0.60  fof(f3,axiom,(
% 0.21/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.60  fof(f2026,plain,(
% 0.21/0.60    spl4_65 | ~spl4_64 | ~spl4_5 | ~spl4_62),
% 0.21/0.60    inference(avatar_split_clause,[],[f2025,f1973,f68,f2011,f2015])).
% 0.21/0.60  fof(f2025,plain,(
% 0.21/0.60    ( ! [X1] : (~r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK2)))) | ~r2_hidden(X1,k3_xboole_0(sK0,sK1))) ) | (~spl4_5 | ~spl4_62)),
% 0.21/0.60    inference(forward_demodulation,[],[f1994,f33])).
% 0.21/0.60  fof(f1994,plain,(
% 0.21/0.60    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,k2_xboole_0(sK2,sK2)),k3_xboole_0(sK1,sK2)))) ) | (~spl4_5 | ~spl4_62)),
% 0.21/0.60    inference(superposition,[],[f248,f1975])).
% 0.21/0.60  fof(f248,plain,(
% 0.21/0.60    ( ! [X8,X7] : (~r2_hidden(X8,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X7))) | ~r1_xboole_0(sK0,k2_xboole_0(X7,k3_xboole_0(sK1,sK2)))) ) | ~spl4_5),
% 0.21/0.60    inference(superposition,[],[f39,f96])).
% 0.21/0.60  fof(f39,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f25])).
% 0.21/0.60  fof(f1976,plain,(
% 0.21/0.60    spl4_62 | ~spl4_23),
% 0.21/0.60    inference(avatar_split_clause,[],[f1940,f329,f1973])).
% 0.21/0.60  fof(f329,plain,(
% 0.21/0.60    spl4_23 <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK2,sK2)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.60  fof(f1940,plain,(
% 0.21/0.60    k3_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(sK2,sK2)))) | ~spl4_23),
% 0.21/0.60    inference(superposition,[],[f349,f37])).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f11])).
% 0.21/0.60  fof(f11,axiom,(
% 0.21/0.60    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.60  fof(f349,plain,(
% 0.21/0.60    ( ! [X2] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)) = k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,k2_xboole_0(sK2,sK2)),X2))) ) | ~spl4_23),
% 0.21/0.60    inference(superposition,[],[f43,f331])).
% 0.21/0.60  fof(f331,plain,(
% 0.21/0.60    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK2,sK2))) | ~spl4_23),
% 0.21/0.60    inference(avatar_component_clause,[],[f329])).
% 0.21/0.60  fof(f1730,plain,(
% 0.21/0.60    spl4_58 | ~spl4_57),
% 0.21/0.60    inference(avatar_split_clause,[],[f1725,f1707,f1727])).
% 0.21/0.60  fof(f1707,plain,(
% 0.21/0.60    spl4_57 <=> r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.21/0.60  fof(f1725,plain,(
% 0.21/0.60    k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) | ~spl4_57),
% 0.21/0.60    inference(resolution,[],[f1709,f41])).
% 0.21/0.60  fof(f41,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f26])).
% 0.21/0.60  fof(f1709,plain,(
% 0.21/0.60    r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) | ~spl4_57),
% 0.21/0.60    inference(avatar_component_clause,[],[f1707])).
% 0.21/0.60  fof(f1715,plain,(
% 0.21/0.60    spl4_57 | ~spl4_5 | ~spl4_55),
% 0.21/0.60    inference(avatar_split_clause,[],[f1697,f1584,f68,f1707])).
% 0.21/0.60  fof(f1584,plain,(
% 0.21/0.60    spl4_55 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.21/0.60  fof(f1697,plain,(
% 0.21/0.60    r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) | (~spl4_5 | ~spl4_55)),
% 0.21/0.60    inference(trivial_inequality_removal,[],[f1688])).
% 0.21/0.60  fof(f1688,plain,(
% 0.21/0.60    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) | (~spl4_5 | ~spl4_55)),
% 0.21/0.60    inference(superposition,[],[f249,f1586])).
% 0.21/0.60  fof(f1586,plain,(
% 0.21/0.60    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | ~spl4_55),
% 0.21/0.60    inference(avatar_component_clause,[],[f1584])).
% 0.21/0.60  fof(f1587,plain,(
% 0.21/0.60    spl4_55 | ~spl4_4 | ~spl4_5),
% 0.21/0.60    inference(avatar_split_clause,[],[f1582,f68,f62,f1584])).
% 0.21/0.60  fof(f62,plain,(
% 0.21/0.60    spl4_4 <=> sK2 = k2_xboole_0(sK0,sK2)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.60  fof(f1582,plain,(
% 0.21/0.60    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | (~spl4_4 | ~spl4_5)),
% 0.21/0.60    inference(forward_demodulation,[],[f1581,f70])).
% 0.21/0.60  fof(f1581,plain,(
% 0.21/0.60    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | (~spl4_4 | ~spl4_5)),
% 0.21/0.60    inference(forward_demodulation,[],[f1555,f34])).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f2])).
% 0.21/0.60  fof(f2,axiom,(
% 0.21/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.60  fof(f1555,plain,(
% 0.21/0.60    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(sK1,sK0))) | (~spl4_4 | ~spl4_5)),
% 0.21/0.60    inference(superposition,[],[f242,f64])).
% 0.21/0.60  fof(f64,plain,(
% 0.21/0.60    sK2 = k2_xboole_0(sK0,sK2) | ~spl4_4),
% 0.21/0.60    inference(avatar_component_clause,[],[f62])).
% 0.21/0.60  fof(f242,plain,(
% 0.21/0.60    ( ! [X2] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(sK1,X2))) = k3_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(X2,sK2)))) ) | ~spl4_5),
% 0.21/0.60    inference(superposition,[],[f96,f43])).
% 0.21/0.60  fof(f1119,plain,(
% 0.21/0.60    spl4_53 | ~spl4_5 | ~spl4_15),
% 0.21/0.60    inference(avatar_split_clause,[],[f1097,f155,f68,f1116])).
% 0.21/0.60  fof(f155,plain,(
% 0.21/0.60    spl4_15 <=> k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,sK1)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.60  fof(f1097,plain,(
% 0.21/0.60    r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl4_5 | ~spl4_15)),
% 0.21/0.60    inference(superposition,[],[f1029,f157])).
% 0.21/0.60  fof(f157,plain,(
% 0.21/0.60    k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,sK1) | ~spl4_15),
% 0.21/0.60    inference(avatar_component_clause,[],[f155])).
% 0.21/0.60  fof(f1029,plain,(
% 0.21/0.60    ( ! [X2] : (r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)),sK0)) ) | ~spl4_5),
% 0.21/0.60    inference(superposition,[],[f32,f147])).
% 0.21/0.60  fof(f147,plain,(
% 0.21/0.60    ( ! [X3] : (sK0 = k2_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X3)),k4_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X3)))) ) | ~spl4_5),
% 0.21/0.60    inference(superposition,[],[f37,f78])).
% 0.21/0.60  fof(f78,plain,(
% 0.21/0.60    ( ! [X1] : (k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X1))) ) | ~spl4_5),
% 0.21/0.60    inference(superposition,[],[f43,f70])).
% 0.21/0.60  fof(f332,plain,(
% 0.21/0.60    spl4_23 | ~spl4_21),
% 0.21/0.60    inference(avatar_split_clause,[],[f327,f311,f329])).
% 0.21/0.60  fof(f311,plain,(
% 0.21/0.60    spl4_21 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK2,sK2)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.60  fof(f327,plain,(
% 0.21/0.60    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK2,sK2))) | ~spl4_21),
% 0.21/0.60    inference(resolution,[],[f313,f41])).
% 0.21/0.60  fof(f313,plain,(
% 0.21/0.60    r1_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK2,sK2))) | ~spl4_21),
% 0.21/0.60    inference(avatar_component_clause,[],[f311])).
% 0.21/0.60  fof(f314,plain,(
% 0.21/0.60    spl4_21 | ~spl4_5 | ~spl4_19),
% 0.21/0.60    inference(avatar_split_clause,[],[f309,f199,f68,f311])).
% 0.21/0.60  fof(f199,plain,(
% 0.21/0.60    spl4_19 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.60  fof(f309,plain,(
% 0.21/0.60    r1_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK2,sK2))) | (~spl4_5 | ~spl4_19)),
% 0.21/0.60    inference(forward_demodulation,[],[f308,f43])).
% 0.21/0.60  fof(f308,plain,(
% 0.21/0.60    r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) | (~spl4_5 | ~spl4_19)),
% 0.21/0.60    inference(trivial_inequality_removal,[],[f307])).
% 0.21/0.60  fof(f307,plain,(
% 0.21/0.60    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) | (~spl4_5 | ~spl4_19)),
% 0.21/0.60    inference(forward_demodulation,[],[f295,f201])).
% 0.21/0.60  fof(f201,plain,(
% 0.21/0.60    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_19),
% 0.21/0.60    inference(avatar_component_clause,[],[f199])).
% 0.21/0.60  fof(f295,plain,(
% 0.21/0.60    k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0) | r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) | ~spl4_5),
% 0.21/0.60    inference(superposition,[],[f150,f70])).
% 0.21/0.60  fof(f150,plain,(
% 0.21/0.60    ( ! [X7] : (k1_xboole_0 != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X7)) | r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X7))) ) | ~spl4_5),
% 0.21/0.60    inference(superposition,[],[f42,f78])).
% 0.21/0.60  fof(f202,plain,(
% 0.21/0.60    spl4_19 | ~spl4_5),
% 0.21/0.60    inference(avatar_split_clause,[],[f197,f68,f199])).
% 0.21/0.60  fof(f197,plain,(
% 0.21/0.60    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_5),
% 0.21/0.60    inference(forward_demodulation,[],[f192,f31])).
% 0.21/0.60  fof(f31,plain,(
% 0.21/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f9])).
% 0.21/0.60  fof(f9,axiom,(
% 0.21/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.60  fof(f192,plain,(
% 0.21/0.60    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k1_xboole_0)) | ~spl4_5),
% 0.21/0.60    inference(superposition,[],[f159,f31])).
% 0.21/0.60  fof(f159,plain,(
% 0.21/0.60    ( ! [X3] : (k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK1,sK2),X3)))) ) | ~spl4_5),
% 0.21/0.60    inference(forward_demodulation,[],[f145,f70])).
% 0.21/0.60  fof(f145,plain,(
% 0.21/0.60    ( ! [X3] : (k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK1,sK2),X3)))) ) | ~spl4_5),
% 0.21/0.60    inference(superposition,[],[f78,f35])).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f7])).
% 0.21/0.60  fof(f7,axiom,(
% 0.21/0.60    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.60  fof(f189,plain,(
% 0.21/0.60    spl4_18 | ~spl4_17),
% 0.21/0.60    inference(avatar_split_clause,[],[f184,f180,f186])).
% 0.21/0.60  fof(f186,plain,(
% 0.21/0.60    spl4_18 <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.60  fof(f180,plain,(
% 0.21/0.60    spl4_17 <=> r1_tarski(k1_xboole_0,k3_xboole_0(sK0,sK1))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.60  fof(f184,plain,(
% 0.21/0.60    k3_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) | ~spl4_17),
% 0.21/0.60    inference(resolution,[],[f182,f40])).
% 0.21/0.60  fof(f182,plain,(
% 0.21/0.60    r1_tarski(k1_xboole_0,k3_xboole_0(sK0,sK1)) | ~spl4_17),
% 0.21/0.60    inference(avatar_component_clause,[],[f180])).
% 0.21/0.60  fof(f183,plain,(
% 0.21/0.60    spl4_17 | ~spl4_15),
% 0.21/0.60    inference(avatar_split_clause,[],[f178,f155,f180])).
% 0.21/0.60  fof(f178,plain,(
% 0.21/0.60    r1_tarski(k1_xboole_0,k3_xboole_0(sK0,sK1)) | ~spl4_15),
% 0.21/0.60    inference(superposition,[],[f32,f157])).
% 0.21/0.60  fof(f158,plain,(
% 0.21/0.60    spl4_15 | ~spl4_5),
% 0.21/0.60    inference(avatar_split_clause,[],[f141,f68,f155])).
% 0.21/0.60  fof(f141,plain,(
% 0.21/0.60    k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,sK1) | ~spl4_5),
% 0.21/0.60    inference(superposition,[],[f78,f37])).
% 0.21/0.60  fof(f71,plain,(
% 0.21/0.60    spl4_5 | ~spl4_1),
% 0.21/0.60    inference(avatar_split_clause,[],[f66,f46,f68])).
% 0.21/0.60  fof(f46,plain,(
% 0.21/0.60    spl4_1 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.60  fof(f66,plain,(
% 0.21/0.60    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl4_1),
% 0.21/0.60    inference(resolution,[],[f48,f41])).
% 0.21/0.60  fof(f48,plain,(
% 0.21/0.60    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl4_1),
% 0.21/0.60    inference(avatar_component_clause,[],[f46])).
% 0.21/0.60  fof(f65,plain,(
% 0.21/0.60    spl4_4 | ~spl4_2),
% 0.21/0.60    inference(avatar_split_clause,[],[f60,f51,f62])).
% 0.21/0.60  fof(f51,plain,(
% 0.21/0.60    spl4_2 <=> r1_tarski(sK0,sK2)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.60  fof(f60,plain,(
% 0.21/0.60    sK2 = k2_xboole_0(sK0,sK2) | ~spl4_2),
% 0.21/0.60    inference(resolution,[],[f53,f40])).
% 0.21/0.60  fof(f53,plain,(
% 0.21/0.60    r1_tarski(sK0,sK2) | ~spl4_2),
% 0.21/0.60    inference(avatar_component_clause,[],[f51])).
% 0.21/0.60  fof(f59,plain,(
% 0.21/0.60    ~spl4_3),
% 0.21/0.60    inference(avatar_split_clause,[],[f27,f56])).
% 0.21/0.60  fof(f27,plain,(
% 0.21/0.60    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.60    inference(cnf_transformation,[],[f23])).
% 0.21/0.60  fof(f23,plain,(
% 0.21/0.60    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f22])).
% 0.21/0.60  fof(f22,plain,(
% 0.21/0.60    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f17,plain,(
% 0.21/0.60    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f15])).
% 0.21/0.60  fof(f15,negated_conjecture,(
% 0.21/0.60    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.60    inference(negated_conjecture,[],[f14])).
% 0.21/0.60  fof(f14,conjecture,(
% 0.21/0.60    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.21/0.60  fof(f54,plain,(
% 0.21/0.60    spl4_2),
% 0.21/0.60    inference(avatar_split_clause,[],[f28,f51])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    r1_tarski(sK0,sK2)),
% 0.21/0.60    inference(cnf_transformation,[],[f23])).
% 0.21/0.60  fof(f49,plain,(
% 0.21/0.60    spl4_1),
% 0.21/0.60    inference(avatar_split_clause,[],[f29,f46])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.60    inference(cnf_transformation,[],[f23])).
% 0.21/0.60  % SZS output end Proof for theBenchmark
% 0.21/0.60  % (20899)------------------------------
% 0.21/0.60  % (20899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (20899)Termination reason: Refutation
% 0.21/0.60  
% 0.21/0.60  % (20899)Memory used [KB]: 12025
% 0.21/0.60  % (20899)Time elapsed: 0.165 s
% 0.21/0.60  % (20899)------------------------------
% 0.21/0.60  % (20899)------------------------------
% 0.21/0.60  % (20887)Success in time 0.25 s
%------------------------------------------------------------------------------
