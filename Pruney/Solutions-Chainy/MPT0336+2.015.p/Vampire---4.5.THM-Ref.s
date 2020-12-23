%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 218 expanded)
%              Number of leaves         :   31 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  302 ( 576 expanded)
%              Number of equality atoms :   36 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f85,f90,f122,f2033,f2077,f2134,f2139,f2143,f3240,f3298,f3318,f3333,f3341,f3343])).

fof(f3343,plain,
    ( ~ spl6_5
    | ~ spl6_9
    | spl6_91 ),
    inference(avatar_contradiction_clause,[],[f3342])).

fof(f3342,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_9
    | spl6_91 ),
    inference(resolution,[],[f3340,f265])).

fof(f265,plain,
    ( ! [X1] : r1_xboole_0(k3_xboole_0(X1,sK1),sK2)
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(superposition,[],[f254,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f254,plain,
    ( ! [X3] : r1_xboole_0(k3_xboole_0(sK1,X3),sK2)
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(resolution,[],[f248,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f248,plain,
    ( ! [X6] : r1_xboole_0(sK2,k3_xboole_0(sK1,X6))
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(trivial_inequality_removal,[],[f246])).

fof(f246,plain,
    ( ! [X6] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(sK2,k3_xboole_0(sK1,X6)) )
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(superposition,[],[f54,f237])).

fof(f237,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK1,X1))
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f108,f129])).

fof(f129,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)
    | ~ spl6_9 ),
    inference(resolution,[],[f124,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f124,plain,
    ( ! [X1] : r1_xboole_0(k1_xboole_0,X1)
    | ~ spl6_9 ),
    inference(resolution,[],[f121,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f121,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_9
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f108,plain,
    ( ! [X1] : k3_xboole_0(sK2,k3_xboole_0(sK1,X1)) = k3_xboole_0(k1_xboole_0,X1)
    | ~ spl6_5 ),
    inference(superposition,[],[f56,f84])).

fof(f84,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_5
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f56,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3340,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | spl6_91 ),
    inference(avatar_component_clause,[],[f3338])).

fof(f3338,plain,
    ( spl6_91
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f3341,plain,
    ( ~ spl6_91
    | ~ spl6_3
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f3334,f3330,f69,f3338])).

fof(f69,plain,
    ( spl6_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f3330,plain,
    ( spl6_90
  <=> r2_hidden(sK3,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f3334,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl6_3
    | ~ spl6_90 ),
    inference(resolution,[],[f3332,f91])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ r1_xboole_0(X0,sK2) )
    | ~ spl6_3 ),
    inference(resolution,[],[f71,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f3332,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK0,sK1))
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f3330])).

fof(f3333,plain,
    ( spl6_90
    | spl6_75 ),
    inference(avatar_split_clause,[],[f3328,f2069,f3330])).

fof(f2069,plain,
    ( spl6_75
  <=> r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f3328,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK0,sK1))
    | spl6_75 ),
    inference(resolution,[],[f2070,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f2070,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))
    | spl6_75 ),
    inference(avatar_component_clause,[],[f2069])).

fof(f3318,plain,
    ( spl6_11
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f3317,f74,f169])).

fof(f169,plain,
    ( spl6_11
  <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f74,plain,
    ( spl6_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f3317,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl6_4 ),
    inference(resolution,[],[f76,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f76,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f3298,plain,
    ( spl6_1
    | ~ spl6_79 ),
    inference(avatar_split_clause,[],[f3292,f3237,f59])).

fof(f59,plain,
    ( spl6_1
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f3237,plain,
    ( spl6_79
  <=> r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f3292,plain,
    ( r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | ~ spl6_79 ),
    inference(resolution,[],[f3239,f52])).

fof(f3239,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl6_79 ),
    inference(avatar_component_clause,[],[f3237])).

fof(f3240,plain,
    ( spl6_79
    | ~ spl6_6
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f3235,f1811,f87,f3237])).

fof(f87,plain,
    ( spl6_6
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1811,plain,
    ( spl6_61
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f3235,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl6_6
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f3230,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f3230,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl6_6
    | ~ spl6_61 ),
    inference(trivial_inequality_removal,[],[f3219])).

fof(f3219,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl6_6
    | ~ spl6_61 ),
    inference(superposition,[],[f233,f1813])).

fof(f1813,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK0)
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f1811])).

fof(f233,plain,
    ( ! [X6] :
        ( k1_xboole_0 != k3_xboole_0(sK1,X6)
        | r1_xboole_0(sK1,k2_xboole_0(sK2,X6)) )
    | ~ spl6_6 ),
    inference(superposition,[],[f54,f92])).

fof(f92,plain,
    ( ! [X0] : k3_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k3_xboole_0(sK1,X0)
    | ~ spl6_6 ),
    inference(resolution,[],[f89,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f89,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f2143,plain,
    ( spl6_61
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f2141,f1803,f1811])).

fof(f1803,plain,
    ( spl6_60
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f2141,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK0)
    | ~ spl6_60 ),
    inference(resolution,[],[f1805,f53])).

fof(f1805,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f1803])).

fof(f2139,plain,
    ( spl6_60
    | ~ spl6_59 ),
    inference(avatar_split_clause,[],[f2137,f1794,f1803])).

fof(f1794,plain,
    ( spl6_59
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f2137,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_59 ),
    inference(resolution,[],[f1796,f52])).

fof(f1796,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f1794])).

fof(f2134,plain,
    ( spl6_59
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f1790,f1069,f1794])).

fof(f1069,plain,
    ( spl6_22
  <=> ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f1790,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_22 ),
    inference(resolution,[],[f1070,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1070,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f1069])).

fof(f2077,plain,
    ( ~ spl6_75
    | spl6_22
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f2063,f1046,f1069,f2069])).

fof(f1046,plain,
    ( spl6_18
  <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f2063,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
        | ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) )
    | ~ spl6_18 ),
    inference(superposition,[],[f46,f1048])).

fof(f1048,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f1046])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2033,plain,
    ( spl6_18
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f2021,f169,f1046])).

fof(f2021,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))
    | ~ spl6_11 ),
    inference(superposition,[],[f41,f171])).

fof(f171,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f169])).

fof(f122,plain,
    ( ~ spl6_2
    | spl6_9
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f106,f82,f120,f64])).

fof(f64,plain,
    ( spl6_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r1_xboole_0(sK2,sK1) )
    | ~ spl6_5 ),
    inference(superposition,[],[f46,f84])).

fof(f90,plain,
    ( spl6_6
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f80,f64,f87])).

fof(f80,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f66,f52])).

fof(f66,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f85,plain,
    ( spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f79,f64,f82])).

fof(f79,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f66,f53])).

fof(f77,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f35,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f72,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f36,f69])).

fof(f36,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f37,f64])).

fof(f37,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f38,f59])).

fof(f38,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:14:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (14532)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (14537)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (14536)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (14542)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (14535)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (14530)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (14546)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (14540)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (14543)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (14544)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (14538)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (14545)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (14533)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (14531)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (14548)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (14534)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (14547)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.54  % (14539)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.55  % (14542)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f3344,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f85,f90,f122,f2033,f2077,f2134,f2139,f2143,f3240,f3298,f3318,f3333,f3341,f3343])).
% 0.21/0.55  fof(f3343,plain,(
% 0.21/0.55    ~spl6_5 | ~spl6_9 | spl6_91),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f3342])).
% 0.21/0.55  fof(f3342,plain,(
% 0.21/0.55    $false | (~spl6_5 | ~spl6_9 | spl6_91)),
% 0.21/0.55    inference(resolution,[],[f3340,f265])).
% 0.21/0.55  fof(f265,plain,(
% 0.21/0.55    ( ! [X1] : (r1_xboole_0(k3_xboole_0(X1,sK1),sK2)) ) | (~spl6_5 | ~spl6_9)),
% 0.21/0.55    inference(superposition,[],[f254,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.55  fof(f254,plain,(
% 0.21/0.55    ( ! [X3] : (r1_xboole_0(k3_xboole_0(sK1,X3),sK2)) ) | (~spl6_5 | ~spl6_9)),
% 0.21/0.55    inference(resolution,[],[f248,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.55  fof(f248,plain,(
% 0.21/0.55    ( ! [X6] : (r1_xboole_0(sK2,k3_xboole_0(sK1,X6))) ) | (~spl6_5 | ~spl6_9)),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f246])).
% 0.21/0.55  fof(f246,plain,(
% 0.21/0.55    ( ! [X6] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK2,k3_xboole_0(sK1,X6))) ) | (~spl6_5 | ~spl6_9)),
% 0.21/0.55    inference(superposition,[],[f54,f237])).
% 0.21/0.55  fof(f237,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK1,X1))) ) | (~spl6_5 | ~spl6_9)),
% 0.21/0.55    inference(forward_demodulation,[],[f108,f129])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) ) | ~spl6_9),
% 0.21/0.55    inference(resolution,[],[f124,f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    ( ! [X1] : (r1_xboole_0(k1_xboole_0,X1)) ) | ~spl6_9),
% 0.21/0.55    inference(resolution,[],[f121,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f120])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    spl6_9 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    ( ! [X1] : (k3_xboole_0(sK2,k3_xboole_0(sK1,X1)) = k3_xboole_0(k1_xboole_0,X1)) ) | ~spl6_5),
% 0.21/0.55    inference(superposition,[],[f56,f84])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl6_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f82])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    spl6_5 <=> k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f3340,plain,(
% 0.21/0.55    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | spl6_91),
% 0.21/0.55    inference(avatar_component_clause,[],[f3338])).
% 0.21/0.55  fof(f3338,plain,(
% 0.21/0.55    spl6_91 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).
% 0.21/0.55  fof(f3341,plain,(
% 0.21/0.55    ~spl6_91 | ~spl6_3 | ~spl6_90),
% 0.21/0.55    inference(avatar_split_clause,[],[f3334,f3330,f69,f3338])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    spl6_3 <=> r2_hidden(sK3,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.55  fof(f3330,plain,(
% 0.21/0.55    spl6_90 <=> r2_hidden(sK3,k3_xboole_0(sK0,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).
% 0.21/0.55  fof(f3334,plain,(
% 0.21/0.55    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | (~spl6_3 | ~spl6_90)),
% 0.21/0.55    inference(resolution,[],[f3332,f91])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) ) | ~spl6_3),
% 0.21/0.55    inference(resolution,[],[f71,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    r2_hidden(sK3,sK2) | ~spl6_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f69])).
% 0.21/0.55  fof(f3332,plain,(
% 0.21/0.55    r2_hidden(sK3,k3_xboole_0(sK0,sK1)) | ~spl6_90),
% 0.21/0.55    inference(avatar_component_clause,[],[f3330])).
% 0.21/0.55  fof(f3333,plain,(
% 0.21/0.55    spl6_90 | spl6_75),
% 0.21/0.55    inference(avatar_split_clause,[],[f3328,f2069,f3330])).
% 0.21/0.55  fof(f2069,plain,(
% 0.21/0.55    spl6_75 <=> r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).
% 0.21/0.55  fof(f3328,plain,(
% 0.21/0.55    r2_hidden(sK3,k3_xboole_0(sK0,sK1)) | spl6_75),
% 0.21/0.55    inference(resolution,[],[f2070,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.55  fof(f2070,plain,(
% 0.21/0.55    ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) | spl6_75),
% 0.21/0.55    inference(avatar_component_clause,[],[f2069])).
% 0.21/0.55  fof(f3318,plain,(
% 0.21/0.55    spl6_11 | ~spl6_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f3317,f74,f169])).
% 0.21/0.55  fof(f169,plain,(
% 0.21/0.55    spl6_11 <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    spl6_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.55  fof(f3317,plain,(
% 0.21/0.55    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl6_4),
% 0.21/0.55    inference(resolution,[],[f76,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl6_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f74])).
% 0.21/0.55  fof(f3298,plain,(
% 0.21/0.55    spl6_1 | ~spl6_79),
% 0.21/0.55    inference(avatar_split_clause,[],[f3292,f3237,f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    spl6_1 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.55  fof(f3237,plain,(
% 0.21/0.55    spl6_79 <=> r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 0.21/0.55  fof(f3292,plain,(
% 0.21/0.55    r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | ~spl6_79),
% 0.21/0.55    inference(resolution,[],[f3239,f52])).
% 0.21/0.55  fof(f3239,plain,(
% 0.21/0.55    r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | ~spl6_79),
% 0.21/0.55    inference(avatar_component_clause,[],[f3237])).
% 0.21/0.55  fof(f3240,plain,(
% 0.21/0.55    spl6_79 | ~spl6_6 | ~spl6_61),
% 0.21/0.55    inference(avatar_split_clause,[],[f3235,f1811,f87,f3237])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    spl6_6 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.55  fof(f1811,plain,(
% 0.21/0.55    spl6_61 <=> k1_xboole_0 = k3_xboole_0(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 0.21/0.55  fof(f3235,plain,(
% 0.21/0.55    r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | (~spl6_6 | ~spl6_61)),
% 0.21/0.55    inference(forward_demodulation,[],[f3230,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.55  fof(f3230,plain,(
% 0.21/0.55    r1_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | (~spl6_6 | ~spl6_61)),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f3219])).
% 0.21/0.55  fof(f3219,plain,(
% 0.21/0.55    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | (~spl6_6 | ~spl6_61)),
% 0.21/0.55    inference(superposition,[],[f233,f1813])).
% 0.21/0.55  fof(f1813,plain,(
% 0.21/0.55    k1_xboole_0 = k3_xboole_0(sK1,sK0) | ~spl6_61),
% 0.21/0.55    inference(avatar_component_clause,[],[f1811])).
% 0.21/0.55  fof(f233,plain,(
% 0.21/0.55    ( ! [X6] : (k1_xboole_0 != k3_xboole_0(sK1,X6) | r1_xboole_0(sK1,k2_xboole_0(sK2,X6))) ) | ~spl6_6),
% 0.21/0.55    inference(superposition,[],[f54,f92])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    ( ! [X0] : (k3_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k3_xboole_0(sK1,X0)) ) | ~spl6_6),
% 0.21/0.55    inference(resolution,[],[f89,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    r1_xboole_0(sK1,sK2) | ~spl6_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f87])).
% 0.21/0.56  fof(f2143,plain,(
% 0.21/0.56    spl6_61 | ~spl6_60),
% 0.21/0.56    inference(avatar_split_clause,[],[f2141,f1803,f1811])).
% 0.21/0.56  fof(f1803,plain,(
% 0.21/0.56    spl6_60 <=> r1_xboole_0(sK1,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 0.21/0.56  fof(f2141,plain,(
% 0.21/0.56    k1_xboole_0 = k3_xboole_0(sK1,sK0) | ~spl6_60),
% 0.21/0.56    inference(resolution,[],[f1805,f53])).
% 0.21/0.56  fof(f1805,plain,(
% 0.21/0.56    r1_xboole_0(sK1,sK0) | ~spl6_60),
% 0.21/0.56    inference(avatar_component_clause,[],[f1803])).
% 0.21/0.56  fof(f2139,plain,(
% 0.21/0.56    spl6_60 | ~spl6_59),
% 0.21/0.56    inference(avatar_split_clause,[],[f2137,f1794,f1803])).
% 0.21/0.56  fof(f1794,plain,(
% 0.21/0.56    spl6_59 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 0.21/0.56  fof(f2137,plain,(
% 0.21/0.56    r1_xboole_0(sK1,sK0) | ~spl6_59),
% 0.21/0.56    inference(resolution,[],[f1796,f52])).
% 0.21/0.56  fof(f1796,plain,(
% 0.21/0.56    r1_xboole_0(sK0,sK1) | ~spl6_59),
% 0.21/0.56    inference(avatar_component_clause,[],[f1794])).
% 0.21/0.56  fof(f2134,plain,(
% 0.21/0.56    spl6_59 | ~spl6_22),
% 0.21/0.56    inference(avatar_split_clause,[],[f1790,f1069,f1794])).
% 0.21/0.56  fof(f1069,plain,(
% 0.21/0.56    spl6_22 <=> ! [X0] : ~r2_hidden(X0,k3_xboole_0(sK0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.56  fof(f1790,plain,(
% 0.21/0.56    r1_xboole_0(sK0,sK1) | ~spl6_22),
% 0.21/0.56    inference(resolution,[],[f1070,f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(rectify,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.56  fof(f1070,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1))) ) | ~spl6_22),
% 0.21/0.56    inference(avatar_component_clause,[],[f1069])).
% 0.21/0.56  fof(f2077,plain,(
% 0.21/0.56    ~spl6_75 | spl6_22 | ~spl6_18),
% 0.21/0.56    inference(avatar_split_clause,[],[f2063,f1046,f1069,f2069])).
% 0.21/0.56  fof(f1046,plain,(
% 0.21/0.56    spl6_18 <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.56  fof(f2063,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))) ) | ~spl6_18),
% 0.21/0.56    inference(superposition,[],[f46,f1048])).
% 0.21/0.56  fof(f1048,plain,(
% 0.21/0.56    k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) | ~spl6_18),
% 0.21/0.56    inference(avatar_component_clause,[],[f1046])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f2033,plain,(
% 0.21/0.56    spl6_18 | ~spl6_11),
% 0.21/0.56    inference(avatar_split_clause,[],[f2021,f169,f1046])).
% 0.21/0.56  fof(f2021,plain,(
% 0.21/0.56    k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) | ~spl6_11),
% 0.21/0.56    inference(superposition,[],[f41,f171])).
% 0.21/0.56  fof(f171,plain,(
% 0.21/0.56    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl6_11),
% 0.21/0.56    inference(avatar_component_clause,[],[f169])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    ~spl6_2 | spl6_9 | ~spl6_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f106,f82,f120,f64])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    spl6_2 <=> r1_xboole_0(sK2,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r1_xboole_0(sK2,sK1)) ) | ~spl6_5),
% 0.21/0.56    inference(superposition,[],[f46,f84])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    spl6_6 | ~spl6_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f80,f64,f87])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    r1_xboole_0(sK1,sK2) | ~spl6_2),
% 0.21/0.56    inference(resolution,[],[f66,f52])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    r1_xboole_0(sK2,sK1) | ~spl6_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f64])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    spl6_5 | ~spl6_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f79,f64,f82])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl6_2),
% 0.21/0.56    inference(resolution,[],[f66,f53])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    spl6_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f35,f74])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.21/0.56    inference(flattening,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.56    inference(negated_conjecture,[],[f16])).
% 0.21/0.56  fof(f16,conjecture,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    spl6_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f36,f69])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    r2_hidden(sK3,sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    spl6_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f37,f64])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    r1_xboole_0(sK2,sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ~spl6_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f38,f59])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (14542)------------------------------
% 0.21/0.56  % (14542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (14542)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (14542)Memory used [KB]: 12409
% 0.21/0.56  % (14542)Time elapsed: 0.118 s
% 0.21/0.56  % (14542)------------------------------
% 0.21/0.56  % (14542)------------------------------
% 0.21/0.56  % (14527)Success in time 0.194 s
%------------------------------------------------------------------------------
