%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 367 expanded)
%              Number of leaves         :   41 ( 135 expanded)
%              Depth                    :   12
%              Number of atoms          :  475 (1605 expanded)
%              Number of equality atoms :  186 ( 923 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f887,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f102,f107,f133,f225,f324,f363,f410,f483,f572,f573,f580,f595,f603,f608,f632,f633,f640,f665,f673,f701,f712,f717,f743,f766,f768,f769,f862,f886])).

fof(f886,plain,
    ( spl7_2
    | ~ spl7_39
    | spl7_50 ),
    inference(avatar_contradiction_clause,[],[f885])).

fof(f885,plain,
    ( $false
    | spl7_2
    | ~ spl7_39
    | spl7_50 ),
    inference(subsumption_resolution,[],[f884,f638])).

fof(f638,plain,
    ( sK1 != sK2
    | spl7_50 ),
    inference(avatar_component_clause,[],[f637])).

fof(f637,plain,
    ( spl7_50
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f884,plain,
    ( sK1 = sK2
    | spl7_2
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f881,f101])).

fof(f101,plain,
    ( sK0 != sK2
    | spl7_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl7_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f881,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl7_39 ),
    inference(resolution,[],[f457,f91])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f457,plain,
    ( r2_hidden(sK2,k2_tarski(sK0,sK1))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl7_39
  <=> r2_hidden(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f862,plain,
    ( ~ spl7_11
    | spl7_23 ),
    inference(avatar_contradiction_clause,[],[f861])).

fof(f861,plain,
    ( $false
    | ~ spl7_11
    | spl7_23 ),
    inference(subsumption_resolution,[],[f850,f285])).

fof(f285,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl7_23
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f850,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_11 ),
    inference(superposition,[],[f108,f216])).

fof(f216,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl7_11
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f108,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f90,f72])).

fof(f72,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f90,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f769,plain,
    ( sK2 != sK3
    | k1_tarski(sK1) != k1_tarski(sK3)
    | k2_tarski(sK2,sK3) != k1_tarski(sK2)
    | k2_tarski(sK0,sK1) != k2_tarski(sK2,sK3)
    | k2_tarski(sK0,sK1) = k1_tarski(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f768,plain,
    ( k1_tarski(sK1) != k1_tarski(sK2)
    | k2_tarski(sK2,sK3) != k1_tarski(sK2)
    | k2_tarski(sK0,sK1) != k2_tarski(sK2,sK3)
    | k2_tarski(sK0,sK1) = k1_tarski(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f766,plain,
    ( ~ spl7_41
    | spl7_54 ),
    inference(avatar_contradiction_clause,[],[f765])).

fof(f765,plain,
    ( $false
    | ~ spl7_41
    | spl7_54 ),
    inference(subsumption_resolution,[],[f759,f72])).

fof(f759,plain,
    ( k1_tarski(sK1) != k2_tarski(sK1,sK1)
    | ~ spl7_41
    | spl7_54 ),
    inference(backward_demodulation,[],[f672,f495])).

fof(f495,plain,
    ( sK1 = sK3
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f493])).

fof(f493,plain,
    ( spl7_41
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f672,plain,
    ( k1_tarski(sK1) != k2_tarski(sK1,sK3)
    | spl7_54 ),
    inference(avatar_component_clause,[],[f670])).

fof(f670,plain,
    ( spl7_54
  <=> k1_tarski(sK1) = k2_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f743,plain,
    ( ~ spl7_53
    | spl7_8
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f742,f637,f201,f661])).

fof(f661,plain,
    ( spl7_53
  <=> k2_tarski(sK0,sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f201,plain,
    ( spl7_8
  <=> k2_tarski(sK0,sK1) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f742,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK1)
    | spl7_8
    | ~ spl7_50 ),
    inference(forward_demodulation,[],[f202,f639])).

fof(f639,plain,
    ( sK1 = sK2
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f637])).

fof(f202,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f201])).

fof(f717,plain,
    ( ~ spl7_18
    | spl7_2
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f659,f637,f99,f260])).

fof(f260,plain,
    ( spl7_18
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f659,plain,
    ( sK0 != sK1
    | spl7_2
    | ~ spl7_50 ),
    inference(superposition,[],[f101,f639])).

% (2762)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f712,plain,
    ( spl7_18
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f707,f696,f260])).

fof(f696,plain,
    ( spl7_56
  <=> r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f707,plain,
    ( sK0 = sK1
    | ~ spl7_56 ),
    inference(resolution,[],[f698,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1
      | X0 = X1 ) ),
    inference(superposition,[],[f91,f72])).

fof(f698,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f696])).

fof(f701,plain,
    ( spl7_56
    | ~ spl7_47
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f700,f637,f541,f696])).

fof(f541,plain,
    ( spl7_47
  <=> r2_hidden(sK0,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f700,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl7_47
    | ~ spl7_50 ),
    inference(forward_demodulation,[],[f543,f639])).

fof(f543,plain,
    ( r2_hidden(sK0,k1_tarski(sK2))
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f541])).

fof(f673,plain,
    ( ~ spl7_54
    | ~ spl7_50
    | spl7_52 ),
    inference(avatar_split_clause,[],[f668,f650,f637,f670])).

fof(f650,plain,
    ( spl7_52
  <=> k2_tarski(sK2,sK3) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f668,plain,
    ( k1_tarski(sK1) != k2_tarski(sK1,sK3)
    | ~ spl7_50
    | spl7_52 ),
    inference(forward_demodulation,[],[f652,f639])).

fof(f652,plain,
    ( k2_tarski(sK2,sK3) != k1_tarski(sK2)
    | spl7_52 ),
    inference(avatar_component_clause,[],[f650])).

fof(f665,plain,
    ( ~ spl7_41
    | spl7_34
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f655,f637,f432,f493])).

fof(f432,plain,
    ( spl7_34
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f655,plain,
    ( sK1 != sK3
    | spl7_34
    | ~ spl7_50 ),
    inference(backward_demodulation,[],[f433,f639])).

fof(f433,plain,
    ( sK2 != sK3
    | spl7_34 ),
    inference(avatar_component_clause,[],[f432])).

fof(f640,plain,
    ( spl7_50
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f634,f536,f637])).

fof(f536,plain,
    ( spl7_46
  <=> r2_hidden(sK1,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f634,plain,
    ( sK1 = sK2
    | ~ spl7_46 ),
    inference(resolution,[],[f538,f163])).

fof(f538,plain,
    ( r2_hidden(sK1,k1_tarski(sK2))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f536])).

fof(f633,plain,
    ( spl7_47
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f621,f201,f541])).

fof(f621,plain,
    ( r2_hidden(sK0,k1_tarski(sK2))
    | ~ spl7_8 ),
    inference(superposition,[],[f90,f203])).

fof(f203,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f201])).

fof(f632,plain,
    ( spl7_46
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f620,f201,f536])).

fof(f620,plain,
    ( r2_hidden(sK1,k1_tarski(sK2))
    | ~ spl7_8 ),
    inference(superposition,[],[f88,f203])).

fof(f88,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f608,plain,
    ( spl7_6
    | spl7_8
    | ~ spl7_3
    | spl7_7
    | spl7_9 ),
    inference(avatar_split_clause,[],[f607,f205,f197,f104,f201,f193])).

fof(f193,plain,
    ( spl7_6
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f104,plain,
    ( spl7_3
  <=> r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f197,plain,
    ( spl7_7
  <=> k1_xboole_0 = k2_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

% (2763)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f205,plain,
    ( spl7_9
  <=> k2_tarski(sK0,sK1) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f607,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)
    | ~ spl7_3
    | spl7_7
    | spl7_9 ),
    inference(subsumption_resolution,[],[f606,f198])).

fof(f198,plain,
    ( k1_xboole_0 != k2_tarski(sK0,sK1)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f197])).

fof(f606,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)
    | ~ spl7_3
    | spl7_9 ),
    inference(subsumption_resolution,[],[f604,f206])).

fof(f206,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK3)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f205])).

fof(f604,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f106,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | k2_tarski(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f106,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f603,plain,
    ( sK1 != sK3
    | k2_tarski(sK2,sK3) != k1_tarski(sK1)
    | k2_tarski(sK0,sK1) != k2_tarski(sK2,sK3)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f595,plain,
    ( spl7_41
    | spl7_1
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f594,f450,f94,f493])).

fof(f94,plain,
    ( spl7_1
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f450,plain,
    ( spl7_38
  <=> r2_hidden(sK3,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f594,plain,
    ( sK1 = sK3
    | spl7_1
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f592,f96])).

fof(f96,plain,
    ( sK0 != sK3
    | spl7_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f592,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl7_38 ),
    inference(resolution,[],[f452,f91])).

fof(f452,plain,
    ( r2_hidden(sK3,k2_tarski(sK0,sK1))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f450])).

fof(f580,plain,
    ( spl7_1
    | ~ spl7_33 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | spl7_1
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f576,f96])).

fof(f576,plain,
    ( sK0 = sK3
    | ~ spl7_33 ),
    inference(resolution,[],[f404,f163])).

fof(f404,plain,
    ( r2_hidden(sK0,k1_tarski(sK3))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl7_33
  <=> r2_hidden(sK0,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f573,plain,
    ( spl7_39
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f566,f193,f455])).

fof(f566,plain,
    ( r2_hidden(sK2,k2_tarski(sK0,sK1))
    | ~ spl7_6 ),
    inference(superposition,[],[f90,f195])).

fof(f195,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f193])).

fof(f572,plain,
    ( spl7_38
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f565,f193,f450])).

fof(f565,plain,
    ( r2_hidden(sK3,k2_tarski(sK0,sK1))
    | ~ spl7_6 ),
    inference(superposition,[],[f88,f195])).

fof(f483,plain,
    ( spl7_33
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f476,f205,f402])).

fof(f476,plain,
    ( r2_hidden(sK0,k1_tarski(sK3))
    | ~ spl7_9 ),
    inference(superposition,[],[f90,f207])).

fof(f207,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f205])).

fof(f410,plain,(
    ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f407,f79])).

fof(f79,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f407,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_24 ),
    inference(resolution,[],[f291,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f76,f70])).

fof(f70,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f291,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl7_24
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f363,plain,(
    ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f360,f79])).

fof(f360,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_23 ),
    inference(resolution,[],[f286,f115])).

fof(f286,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f284])).

fof(f324,plain,
    ( spl7_24
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f315,f197,f289])).

fof(f315,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl7_7 ),
    inference(superposition,[],[f90,f199])).

fof(f199,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f197])).

fof(f225,plain,
    ( spl7_10
    | spl7_11
    | spl7_12
    | spl7_13
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f188,f130,f222,f218,f214,f210])).

fof(f210,plain,
    ( spl7_10
  <=> k2_tarski(sK2,sK3) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f218,plain,
    ( spl7_12
  <=> k1_tarski(sK1) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f222,plain,
    ( spl7_13
  <=> k1_tarski(sK1) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f130,plain,
    ( spl7_4
  <=> r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f188,plain,
    ( k1_tarski(sK1) = k1_tarski(sK3)
    | k1_tarski(sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k1_tarski(sK1)
    | k2_tarski(sK2,sK3) = k1_tarski(sK1)
    | ~ spl7_4 ),
    inference(resolution,[],[f55,f132])).

fof(f132,plain,
    ( r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f133,plain,
    ( spl7_4
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f127,f104,f130])).

fof(f127,plain,
    ( r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))
    | ~ spl7_3 ),
    inference(resolution,[],[f118,f84])).

fof(f84,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_tarski(sK0,sK1))
        | r1_tarski(X0,k2_tarski(sK2,sK3)) )
    | ~ spl7_3 ),
    inference(resolution,[],[f73,f106])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f107,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f48,f104])).

fof(f48,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f102,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f49,f99])).

fof(f49,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f97,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f50,f94])).

fof(f50,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (2772)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.48  % (2780)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (2780)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (2761)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f887,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f97,f102,f107,f133,f225,f324,f363,f410,f483,f572,f573,f580,f595,f603,f608,f632,f633,f640,f665,f673,f701,f712,f717,f743,f766,f768,f769,f862,f886])).
% 0.20/0.53  fof(f886,plain,(
% 0.20/0.53    spl7_2 | ~spl7_39 | spl7_50),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f885])).
% 0.20/0.53  fof(f885,plain,(
% 0.20/0.53    $false | (spl7_2 | ~spl7_39 | spl7_50)),
% 0.20/0.53    inference(subsumption_resolution,[],[f884,f638])).
% 0.20/0.53  fof(f638,plain,(
% 0.20/0.53    sK1 != sK2 | spl7_50),
% 0.20/0.53    inference(avatar_component_clause,[],[f637])).
% 0.20/0.53  fof(f637,plain,(
% 0.20/0.53    spl7_50 <=> sK1 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 0.20/0.53  fof(f884,plain,(
% 0.20/0.53    sK1 = sK2 | (spl7_2 | ~spl7_39)),
% 0.20/0.53    inference(subsumption_resolution,[],[f881,f101])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    sK0 != sK2 | spl7_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f99])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    spl7_2 <=> sK0 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.53  fof(f881,plain,(
% 0.20/0.53    sK0 = sK2 | sK1 = sK2 | ~spl7_39),
% 0.20/0.53    inference(resolution,[],[f457,f91])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.20/0.53    inference(equality_resolution,[],[f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(rectify,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(flattening,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.53  fof(f457,plain,(
% 0.20/0.53    r2_hidden(sK2,k2_tarski(sK0,sK1)) | ~spl7_39),
% 0.20/0.53    inference(avatar_component_clause,[],[f455])).
% 0.20/0.53  fof(f455,plain,(
% 0.20/0.53    spl7_39 <=> r2_hidden(sK2,k2_tarski(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.20/0.53  fof(f862,plain,(
% 0.20/0.53    ~spl7_11 | spl7_23),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f861])).
% 0.20/0.53  fof(f861,plain,(
% 0.20/0.53    $false | (~spl7_11 | spl7_23)),
% 0.20/0.53    inference(subsumption_resolution,[],[f850,f285])).
% 0.20/0.53  fof(f285,plain,(
% 0.20/0.53    ~r2_hidden(sK1,k1_xboole_0) | spl7_23),
% 0.20/0.53    inference(avatar_component_clause,[],[f284])).
% 0.20/0.53  fof(f284,plain,(
% 0.20/0.53    spl7_23 <=> r2_hidden(sK1,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.20/0.53  fof(f850,plain,(
% 0.20/0.53    r2_hidden(sK1,k1_xboole_0) | ~spl7_11),
% 0.20/0.53    inference(superposition,[],[f108,f216])).
% 0.20/0.53  fof(f216,plain,(
% 0.20/0.53    k1_xboole_0 = k1_tarski(sK1) | ~spl7_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f214])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    spl7_11 <=> k1_xboole_0 = k1_tarski(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.20/0.53    inference(superposition,[],[f90,f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 0.20/0.53    inference(equality_resolution,[],[f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f769,plain,(
% 0.20/0.53    sK2 != sK3 | k1_tarski(sK1) != k1_tarski(sK3) | k2_tarski(sK2,sK3) != k1_tarski(sK2) | k2_tarski(sK0,sK1) != k2_tarski(sK2,sK3) | k2_tarski(sK0,sK1) = k1_tarski(sK1)),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f768,plain,(
% 0.20/0.53    k1_tarski(sK1) != k1_tarski(sK2) | k2_tarski(sK2,sK3) != k1_tarski(sK2) | k2_tarski(sK0,sK1) != k2_tarski(sK2,sK3) | k2_tarski(sK0,sK1) = k1_tarski(sK1)),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f766,plain,(
% 0.20/0.53    ~spl7_41 | spl7_54),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f765])).
% 0.20/0.53  fof(f765,plain,(
% 0.20/0.53    $false | (~spl7_41 | spl7_54)),
% 0.20/0.53    inference(subsumption_resolution,[],[f759,f72])).
% 0.20/0.53  fof(f759,plain,(
% 0.20/0.53    k1_tarski(sK1) != k2_tarski(sK1,sK1) | (~spl7_41 | spl7_54)),
% 0.20/0.53    inference(backward_demodulation,[],[f672,f495])).
% 0.20/0.53  fof(f495,plain,(
% 0.20/0.53    sK1 = sK3 | ~spl7_41),
% 0.20/0.53    inference(avatar_component_clause,[],[f493])).
% 0.20/0.53  fof(f493,plain,(
% 0.20/0.53    spl7_41 <=> sK1 = sK3),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.20/0.53  fof(f672,plain,(
% 0.20/0.53    k1_tarski(sK1) != k2_tarski(sK1,sK3) | spl7_54),
% 0.20/0.53    inference(avatar_component_clause,[],[f670])).
% 0.20/0.53  fof(f670,plain,(
% 0.20/0.53    spl7_54 <=> k1_tarski(sK1) = k2_tarski(sK1,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).
% 0.20/0.53  fof(f743,plain,(
% 0.20/0.53    ~spl7_53 | spl7_8 | ~spl7_50),
% 0.20/0.53    inference(avatar_split_clause,[],[f742,f637,f201,f661])).
% 0.20/0.53  fof(f661,plain,(
% 0.20/0.53    spl7_53 <=> k2_tarski(sK0,sK1) = k1_tarski(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    spl7_8 <=> k2_tarski(sK0,sK1) = k1_tarski(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.53  fof(f742,plain,(
% 0.20/0.53    k2_tarski(sK0,sK1) != k1_tarski(sK1) | (spl7_8 | ~spl7_50)),
% 0.20/0.53    inference(forward_demodulation,[],[f202,f639])).
% 0.20/0.53  fof(f639,plain,(
% 0.20/0.53    sK1 = sK2 | ~spl7_50),
% 0.20/0.53    inference(avatar_component_clause,[],[f637])).
% 0.20/0.53  fof(f202,plain,(
% 0.20/0.53    k2_tarski(sK0,sK1) != k1_tarski(sK2) | spl7_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f201])).
% 0.20/0.53  fof(f717,plain,(
% 0.20/0.53    ~spl7_18 | spl7_2 | ~spl7_50),
% 0.20/0.53    inference(avatar_split_clause,[],[f659,f637,f99,f260])).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    spl7_18 <=> sK0 = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.53  fof(f659,plain,(
% 0.20/0.53    sK0 != sK1 | (spl7_2 | ~spl7_50)),
% 0.20/0.53    inference(superposition,[],[f101,f639])).
% 0.20/0.53  % (2762)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  fof(f712,plain,(
% 0.20/0.53    spl7_18 | ~spl7_56),
% 0.20/0.53    inference(avatar_split_clause,[],[f707,f696,f260])).
% 0.20/0.53  fof(f696,plain,(
% 0.20/0.53    spl7_56 <=> r2_hidden(sK0,k1_tarski(sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 0.20/0.53  fof(f707,plain,(
% 0.20/0.53    sK0 = sK1 | ~spl7_56),
% 0.20/0.53    inference(resolution,[],[f698,f163])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f162])).
% 0.20/0.53  fof(f162,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1 | X0 = X1) )),
% 0.20/0.53    inference(superposition,[],[f91,f72])).
% 0.20/0.53  fof(f698,plain,(
% 0.20/0.53    r2_hidden(sK0,k1_tarski(sK1)) | ~spl7_56),
% 0.20/0.53    inference(avatar_component_clause,[],[f696])).
% 0.20/0.53  fof(f701,plain,(
% 0.20/0.53    spl7_56 | ~spl7_47 | ~spl7_50),
% 0.20/0.53    inference(avatar_split_clause,[],[f700,f637,f541,f696])).
% 0.20/0.53  fof(f541,plain,(
% 0.20/0.53    spl7_47 <=> r2_hidden(sK0,k1_tarski(sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 0.20/0.53  fof(f700,plain,(
% 0.20/0.53    r2_hidden(sK0,k1_tarski(sK1)) | (~spl7_47 | ~spl7_50)),
% 0.20/0.53    inference(forward_demodulation,[],[f543,f639])).
% 0.20/0.53  fof(f543,plain,(
% 0.20/0.53    r2_hidden(sK0,k1_tarski(sK2)) | ~spl7_47),
% 0.20/0.53    inference(avatar_component_clause,[],[f541])).
% 0.20/0.53  fof(f673,plain,(
% 0.20/0.53    ~spl7_54 | ~spl7_50 | spl7_52),
% 0.20/0.53    inference(avatar_split_clause,[],[f668,f650,f637,f670])).
% 0.20/0.53  fof(f650,plain,(
% 0.20/0.53    spl7_52 <=> k2_tarski(sK2,sK3) = k1_tarski(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 0.20/0.53  fof(f668,plain,(
% 0.20/0.53    k1_tarski(sK1) != k2_tarski(sK1,sK3) | (~spl7_50 | spl7_52)),
% 0.20/0.53    inference(forward_demodulation,[],[f652,f639])).
% 0.20/0.53  fof(f652,plain,(
% 0.20/0.53    k2_tarski(sK2,sK3) != k1_tarski(sK2) | spl7_52),
% 0.20/0.53    inference(avatar_component_clause,[],[f650])).
% 0.20/0.53  fof(f665,plain,(
% 0.20/0.53    ~spl7_41 | spl7_34 | ~spl7_50),
% 0.20/0.53    inference(avatar_split_clause,[],[f655,f637,f432,f493])).
% 0.20/0.53  fof(f432,plain,(
% 0.20/0.53    spl7_34 <=> sK2 = sK3),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.20/0.53  fof(f655,plain,(
% 0.20/0.53    sK1 != sK3 | (spl7_34 | ~spl7_50)),
% 0.20/0.53    inference(backward_demodulation,[],[f433,f639])).
% 0.20/0.53  fof(f433,plain,(
% 0.20/0.53    sK2 != sK3 | spl7_34),
% 0.20/0.53    inference(avatar_component_clause,[],[f432])).
% 0.20/0.53  fof(f640,plain,(
% 0.20/0.53    spl7_50 | ~spl7_46),
% 0.20/0.53    inference(avatar_split_clause,[],[f634,f536,f637])).
% 0.20/0.53  fof(f536,plain,(
% 0.20/0.53    spl7_46 <=> r2_hidden(sK1,k1_tarski(sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 0.20/0.53  fof(f634,plain,(
% 0.20/0.53    sK1 = sK2 | ~spl7_46),
% 0.20/0.53    inference(resolution,[],[f538,f163])).
% 0.20/0.53  fof(f538,plain,(
% 0.20/0.53    r2_hidden(sK1,k1_tarski(sK2)) | ~spl7_46),
% 0.20/0.53    inference(avatar_component_clause,[],[f536])).
% 0.20/0.53  fof(f633,plain,(
% 0.20/0.53    spl7_47 | ~spl7_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f621,f201,f541])).
% 0.20/0.53  fof(f621,plain,(
% 0.20/0.53    r2_hidden(sK0,k1_tarski(sK2)) | ~spl7_8),
% 0.20/0.53    inference(superposition,[],[f90,f203])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    k2_tarski(sK0,sK1) = k1_tarski(sK2) | ~spl7_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f201])).
% 0.20/0.53  fof(f632,plain,(
% 0.20/0.53    spl7_46 | ~spl7_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f620,f201,f536])).
% 0.20/0.53  fof(f620,plain,(
% 0.20/0.53    r2_hidden(sK1,k1_tarski(sK2)) | ~spl7_8),
% 0.20/0.53    inference(superposition,[],[f88,f203])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.20/0.53    inference(equality_resolution,[],[f87])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.20/0.53    inference(equality_resolution,[],[f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f608,plain,(
% 0.20/0.53    spl7_6 | spl7_8 | ~spl7_3 | spl7_7 | spl7_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f607,f205,f197,f104,f201,f193])).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    spl7_6 <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    spl7_3 <=> r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.53  fof(f197,plain,(
% 0.20/0.53    spl7_7 <=> k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.53  % (2763)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  fof(f205,plain,(
% 0.20/0.53    spl7_9 <=> k2_tarski(sK0,sK1) = k1_tarski(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.53  fof(f607,plain,(
% 0.20/0.53    k2_tarski(sK0,sK1) = k1_tarski(sK2) | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) | (~spl7_3 | spl7_7 | spl7_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f606,f198])).
% 0.20/0.53  fof(f198,plain,(
% 0.20/0.53    k1_xboole_0 != k2_tarski(sK0,sK1) | spl7_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f197])).
% 0.20/0.53  fof(f606,plain,(
% 0.20/0.53    k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) | (~spl7_3 | spl7_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f604,f206])).
% 0.20/0.53  fof(f206,plain,(
% 0.20/0.53    k2_tarski(sK0,sK1) != k1_tarski(sK3) | spl7_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f205])).
% 0.20/0.53  fof(f604,plain,(
% 0.20/0.53    k2_tarski(sK0,sK1) = k1_tarski(sK3) | k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) | ~spl7_3),
% 0.20/0.53    inference(resolution,[],[f106,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k2_tarski(X1,X2) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.20/0.53    inference(flattening,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.20/0.53    inference(nnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) | ~spl7_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f104])).
% 0.20/0.53  fof(f603,plain,(
% 0.20/0.53    sK1 != sK3 | k2_tarski(sK2,sK3) != k1_tarski(sK1) | k2_tarski(sK0,sK1) != k2_tarski(sK2,sK3) | k2_tarski(sK0,sK1) = k1_tarski(sK3)),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f595,plain,(
% 0.20/0.53    spl7_41 | spl7_1 | ~spl7_38),
% 0.20/0.53    inference(avatar_split_clause,[],[f594,f450,f94,f493])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    spl7_1 <=> sK0 = sK3),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.53  fof(f450,plain,(
% 0.20/0.53    spl7_38 <=> r2_hidden(sK3,k2_tarski(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.20/0.53  fof(f594,plain,(
% 0.20/0.53    sK1 = sK3 | (spl7_1 | ~spl7_38)),
% 0.20/0.53    inference(subsumption_resolution,[],[f592,f96])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    sK0 != sK3 | spl7_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f94])).
% 0.20/0.53  fof(f592,plain,(
% 0.20/0.53    sK0 = sK3 | sK1 = sK3 | ~spl7_38),
% 0.20/0.53    inference(resolution,[],[f452,f91])).
% 0.20/0.53  fof(f452,plain,(
% 0.20/0.53    r2_hidden(sK3,k2_tarski(sK0,sK1)) | ~spl7_38),
% 0.20/0.53    inference(avatar_component_clause,[],[f450])).
% 0.20/0.53  fof(f580,plain,(
% 0.20/0.53    spl7_1 | ~spl7_33),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f579])).
% 0.20/0.53  fof(f579,plain,(
% 0.20/0.53    $false | (spl7_1 | ~spl7_33)),
% 0.20/0.53    inference(subsumption_resolution,[],[f576,f96])).
% 0.20/0.53  fof(f576,plain,(
% 0.20/0.53    sK0 = sK3 | ~spl7_33),
% 0.20/0.53    inference(resolution,[],[f404,f163])).
% 0.20/0.53  fof(f404,plain,(
% 0.20/0.53    r2_hidden(sK0,k1_tarski(sK3)) | ~spl7_33),
% 0.20/0.53    inference(avatar_component_clause,[],[f402])).
% 0.20/0.53  fof(f402,plain,(
% 0.20/0.53    spl7_33 <=> r2_hidden(sK0,k1_tarski(sK3))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.20/0.53  fof(f573,plain,(
% 0.20/0.53    spl7_39 | ~spl7_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f566,f193,f455])).
% 0.20/0.53  fof(f566,plain,(
% 0.20/0.53    r2_hidden(sK2,k2_tarski(sK0,sK1)) | ~spl7_6),
% 0.20/0.53    inference(superposition,[],[f90,f195])).
% 0.20/0.53  fof(f195,plain,(
% 0.20/0.53    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) | ~spl7_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f193])).
% 0.20/0.53  fof(f572,plain,(
% 0.20/0.53    spl7_38 | ~spl7_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f565,f193,f450])).
% 0.20/0.53  fof(f565,plain,(
% 0.20/0.53    r2_hidden(sK3,k2_tarski(sK0,sK1)) | ~spl7_6),
% 0.20/0.53    inference(superposition,[],[f88,f195])).
% 0.20/0.53  fof(f483,plain,(
% 0.20/0.53    spl7_33 | ~spl7_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f476,f205,f402])).
% 0.20/0.53  fof(f476,plain,(
% 0.20/0.53    r2_hidden(sK0,k1_tarski(sK3)) | ~spl7_9),
% 0.20/0.53    inference(superposition,[],[f90,f207])).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    k2_tarski(sK0,sK1) = k1_tarski(sK3) | ~spl7_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f205])).
% 0.20/0.53  fof(f410,plain,(
% 0.20/0.53    ~spl7_24),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f409])).
% 0.20/0.53  fof(f409,plain,(
% 0.20/0.53    $false | ~spl7_24),
% 0.20/0.53    inference(subsumption_resolution,[],[f407,f79])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.53  fof(f407,plain,(
% 0.20/0.53    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl7_24),
% 0.20/0.53    inference(resolution,[],[f291,f115])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r1_xboole_0(X0,X0)) )),
% 0.20/0.53    inference(superposition,[],[f76,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.53    inference(rectify,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.53  fof(f291,plain,(
% 0.20/0.53    r2_hidden(sK0,k1_xboole_0) | ~spl7_24),
% 0.20/0.53    inference(avatar_component_clause,[],[f289])).
% 0.20/0.53  fof(f289,plain,(
% 0.20/0.53    spl7_24 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.20/0.53  fof(f363,plain,(
% 0.20/0.53    ~spl7_23),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f362])).
% 0.20/0.53  fof(f362,plain,(
% 0.20/0.53    $false | ~spl7_23),
% 0.20/0.53    inference(subsumption_resolution,[],[f360,f79])).
% 0.20/0.53  fof(f360,plain,(
% 0.20/0.53    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl7_23),
% 0.20/0.53    inference(resolution,[],[f286,f115])).
% 0.20/0.53  fof(f286,plain,(
% 0.20/0.53    r2_hidden(sK1,k1_xboole_0) | ~spl7_23),
% 0.20/0.53    inference(avatar_component_clause,[],[f284])).
% 0.20/0.53  fof(f324,plain,(
% 0.20/0.53    spl7_24 | ~spl7_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f315,f197,f289])).
% 0.20/0.53  fof(f315,plain,(
% 0.20/0.53    r2_hidden(sK0,k1_xboole_0) | ~spl7_7),
% 0.20/0.53    inference(superposition,[],[f90,f199])).
% 0.20/0.53  fof(f199,plain,(
% 0.20/0.53    k1_xboole_0 = k2_tarski(sK0,sK1) | ~spl7_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f197])).
% 0.20/0.53  fof(f225,plain,(
% 0.20/0.53    spl7_10 | spl7_11 | spl7_12 | spl7_13 | ~spl7_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f188,f130,f222,f218,f214,f210])).
% 0.20/0.53  fof(f210,plain,(
% 0.20/0.53    spl7_10 <=> k2_tarski(sK2,sK3) = k1_tarski(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.53  fof(f218,plain,(
% 0.20/0.53    spl7_12 <=> k1_tarski(sK1) = k1_tarski(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.53  fof(f222,plain,(
% 0.20/0.53    spl7_13 <=> k1_tarski(sK1) = k1_tarski(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    spl7_4 <=> r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    k1_tarski(sK1) = k1_tarski(sK3) | k1_tarski(sK1) = k1_tarski(sK2) | k1_xboole_0 = k1_tarski(sK1) | k2_tarski(sK2,sK3) = k1_tarski(sK1) | ~spl7_4),
% 0.20/0.53    inference(resolution,[],[f55,f132])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) | ~spl7_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f130])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    spl7_4 | ~spl7_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f127,f104,f130])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) | ~spl7_3),
% 0.20/0.53    inference(resolution,[],[f118,f84])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k2_tarski(X1,X2))) )),
% 0.20/0.53    inference(equality_resolution,[],[f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,k2_tarski(sK0,sK1)) | r1_tarski(X0,k2_tarski(sK2,sK3))) ) | ~spl7_3),
% 0.20/0.53    inference(resolution,[],[f73,f106])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    spl7_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f48,f104])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.53    inference(ennf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.53    inference(negated_conjecture,[],[f21])).
% 0.20/0.53  fof(f21,conjecture,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    ~spl7_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f49,f99])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    sK0 != sK2),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ~spl7_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f50,f94])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    sK0 != sK3),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (2780)------------------------------
% 0.20/0.53  % (2780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2780)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (2780)Memory used [KB]: 6780
% 0.20/0.53  % (2780)Time elapsed: 0.121 s
% 0.20/0.53  % (2780)------------------------------
% 0.20/0.53  % (2780)------------------------------
% 0.20/0.54  % (2758)Success in time 0.178 s
%------------------------------------------------------------------------------
