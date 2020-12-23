%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:06 EST 2020

% Result     : Theorem 5.39s
% Output     : Refutation 5.39s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 273 expanded)
%              Number of leaves         :   19 (  77 expanded)
%              Depth                    :   21
%              Number of atoms          :  318 (1193 expanded)
%              Number of equality atoms :   63 ( 207 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20801,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1759,f5256,f8310,f8476,f15194,f20800])).

fof(f20800,plain,
    ( ~ spl4_9
    | spl4_10
    | ~ spl4_93 ),
    inference(avatar_contradiction_clause,[],[f20799])).

fof(f20799,plain,
    ( $false
    | ~ spl4_9
    | spl4_10
    | ~ spl4_93 ),
    inference(subsumption_resolution,[],[f20798,f20406])).

fof(f20406,plain,
    ( ! [X6,X5] : r1_tarski(k3_xboole_0(X5,X6),X5)
    | ~ spl4_93 ),
    inference(superposition,[],[f20375,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f20375,plain,
    ( ! [X180,X179] : r1_tarski(X179,k2_xboole_0(X180,X179))
    | ~ spl4_93 ),
    inference(trivial_inequality_removal,[],[f20298])).

fof(f20298,plain,
    ( ! [X180,X179] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(X179,k2_xboole_0(X180,X179)) )
    | ~ spl4_93 ),
    inference(superposition,[],[f37,f19040])).

fof(f19040,plain,
    ( ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,X8))
    | ~ spl4_93 ),
    inference(forward_demodulation,[],[f18748,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f18748,plain,
    ( ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9)))
    | ~ spl4_93 ),
    inference(superposition,[],[f18734,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f18734,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3)
    | ~ spl4_93 ),
    inference(subsumption_resolution,[],[f18731,f5398])).

fof(f5398,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_93 ),
    inference(duplicate_literal_removal,[],[f5396])).

fof(f5396,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl4_93 ),
    inference(resolution,[],[f5395,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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

fof(f5395,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_93 ),
    inference(trivial_inequality_removal,[],[f5394])).

fof(f5394,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_93 ),
    inference(superposition,[],[f56,f5366])).

fof(f5366,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_93 ),
    inference(resolution,[],[f5354,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f5354,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_93 ),
    inference(superposition,[],[f54,f5270])).

fof(f5270,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_93 ),
    inference(forward_demodulation,[],[f5262,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f5262,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_93 ),
    inference(superposition,[],[f40,f5157])).

fof(f5157,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_93 ),
    inference(avatar_component_clause,[],[f5156])).

fof(f5156,plain,
    ( spl4_93
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f18731,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k4_xboole_0(X3,X3)
        | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0) )
    | ~ spl4_93 ),
    inference(duplicate_literal_removal,[],[f18670])).

fof(f18670,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k4_xboole_0(X3,X3)
        | k1_xboole_0 = k4_xboole_0(X3,X3)
        | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0) )
    | ~ spl4_93 ),
    inference(resolution,[],[f5400,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f5400,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK2(X2,X3,k1_xboole_0),X2)
        | k1_xboole_0 = k4_xboole_0(X2,X3) )
    | ~ spl4_93 ),
    inference(resolution,[],[f5398,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f20798,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl4_9
    | spl4_10
    | ~ spl4_93 ),
    inference(subsumption_resolution,[],[f4568,f5398])).

fof(f4568,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl4_9
    | spl4_10 ),
    inference(superposition,[],[f2474,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2474,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0))
    | ~ spl4_9
    | spl4_10 ),
    inference(resolution,[],[f647,f170])).

fof(f170,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl4_9
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f647,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)
        | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,sK0)) )
    | spl4_10 ),
    inference(resolution,[],[f173,f60])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f173,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_10
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f15194,plain,
    ( spl4_9
    | spl4_10 ),
    inference(avatar_split_clause,[],[f15193,f172,f168])).

fof(f15193,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f34,f51])).

fof(f34,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f8476,plain,
    ( ~ spl4_10
    | spl4_17
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f639,f168,f641,f172])).

fof(f641,plain,
    ( spl4_17
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f639,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f628,f34])).

fof(f628,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f170,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8310,plain,
    ( spl4_9
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f8309])).

fof(f8309,plain,
    ( $false
    | spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f8308,f7611])).

fof(f7611,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl4_9 ),
    inference(subsumption_resolution,[],[f7602,f34])).

fof(f7602,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl4_9 ),
    inference(resolution,[],[f169,f52])).

fof(f169,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f168])).

fof(f8308,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl4_9
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f8289,f40])).

fof(f8289,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl4_9
    | ~ spl4_10 ),
    inference(resolution,[],[f7604,f174])).

fof(f174,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f172])).

fof(f7604,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)
        | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1))) )
    | spl4_9 ),
    inference(resolution,[],[f169,f60])).

fof(f5256,plain,(
    spl4_93 ),
    inference(avatar_contradiction_clause,[],[f5255])).

fof(f5255,plain,
    ( $false
    | spl4_93 ),
    inference(subsumption_resolution,[],[f5247,f5164])).

fof(f5164,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | spl4_93 ),
    inference(trivial_inequality_removal,[],[f5161])).

fof(f5161,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,sK0)
    | spl4_93 ),
    inference(superposition,[],[f5158,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5158,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK0)
    | spl4_93 ),
    inference(avatar_component_clause,[],[f5156])).

fof(f5247,plain,
    ( r1_xboole_0(k1_xboole_0,sK0)
    | spl4_93 ),
    inference(resolution,[],[f5207,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5207,plain,
    ( ! [X2] : ~ r2_hidden(sK3(k1_xboole_0,sK0),X2)
    | spl4_93 ),
    inference(forward_demodulation,[],[f5205,f46])).

fof(f5205,plain,
    ( ! [X2] : ~ r2_hidden(sK3(k1_xboole_0,sK0),k4_xboole_0(X2,k1_xboole_0))
    | spl4_93 ),
    inference(resolution,[],[f5185,f61])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5185,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK0),k1_xboole_0)
    | spl4_93 ),
    inference(resolution,[],[f5164,f57])).

fof(f1759,plain,
    ( ~ spl4_9
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f1758])).

fof(f1758,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f1752,f643])).

fof(f643,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f641])).

fof(f1752,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl4_9 ),
    inference(superposition,[],[f631,f40])).

fof(f631,plain,
    ( ! [X2] : ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X2,k3_xboole_0(sK0,sK1)))
    | ~ spl4_9 ),
    inference(resolution,[],[f170,f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:12:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.46  % (8222)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.46  % (8222)Refutation not found, incomplete strategy% (8222)------------------------------
% 0.19/0.46  % (8222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (8222)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (8222)Memory used [KB]: 10618
% 0.19/0.46  % (8222)Time elapsed: 0.054 s
% 0.19/0.46  % (8222)------------------------------
% 0.19/0.46  % (8222)------------------------------
% 0.19/0.46  % (8229)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.46  % (8225)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.46  % (8215)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.47  % (8217)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.48  % (8223)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.48  % (8223)Refutation not found, incomplete strategy% (8223)------------------------------
% 0.19/0.48  % (8223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (8223)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (8223)Memory used [KB]: 6012
% 0.19/0.48  % (8223)Time elapsed: 0.002 s
% 0.19/0.48  % (8223)------------------------------
% 0.19/0.48  % (8223)------------------------------
% 0.19/0.48  % (8227)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.49  % (8224)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.49  % (8219)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.49  % (8212)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (8212)Refutation not found, incomplete strategy% (8212)------------------------------
% 0.19/0.49  % (8212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (8213)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.49  % (8212)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (8212)Memory used [KB]: 10618
% 0.19/0.49  % (8212)Time elapsed: 0.087 s
% 0.19/0.49  % (8212)------------------------------
% 0.19/0.49  % (8212)------------------------------
% 0.19/0.49  % (8214)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (8214)Refutation not found, incomplete strategy% (8214)------------------------------
% 0.19/0.50  % (8214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (8214)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (8214)Memory used [KB]: 10618
% 0.19/0.50  % (8214)Time elapsed: 0.082 s
% 0.19/0.50  % (8214)------------------------------
% 0.19/0.50  % (8214)------------------------------
% 0.19/0.50  % (8211)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.50  % (8211)Refutation not found, incomplete strategy% (8211)------------------------------
% 0.19/0.50  % (8211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (8211)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (8211)Memory used [KB]: 6140
% 0.19/0.50  % (8211)Time elapsed: 0.091 s
% 0.19/0.50  % (8211)------------------------------
% 0.19/0.50  % (8211)------------------------------
% 0.19/0.50  % (8216)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.50  % (8230)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.19/0.50  % (8228)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.50  % (8231)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.51  % (8231)Refutation not found, incomplete strategy% (8231)------------------------------
% 0.19/0.51  % (8231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (8231)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (8231)Memory used [KB]: 10618
% 0.19/0.51  % (8231)Time elapsed: 0.102 s
% 0.19/0.51  % (8231)------------------------------
% 0.19/0.51  % (8231)------------------------------
% 0.19/0.51  % (8218)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.51  % (8224)Refutation not found, incomplete strategy% (8224)------------------------------
% 0.19/0.51  % (8224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (8224)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (8224)Memory used [KB]: 1663
% 0.19/0.51  % (8224)Time elapsed: 0.102 s
% 0.19/0.51  % (8224)------------------------------
% 0.19/0.51  % (8224)------------------------------
% 0.19/0.51  % (8221)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.51  % (8221)Refutation not found, incomplete strategy% (8221)------------------------------
% 0.19/0.51  % (8221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (8221)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (8221)Memory used [KB]: 6012
% 0.19/0.51  % (8221)Time elapsed: 0.104 s
% 0.19/0.51  % (8221)------------------------------
% 0.19/0.51  % (8221)------------------------------
% 0.19/0.51  % (8220)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.51  % (8226)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.51  % (8226)Refutation not found, incomplete strategy% (8226)------------------------------
% 0.19/0.51  % (8226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (8226)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (8226)Memory used [KB]: 6140
% 0.19/0.51  % (8226)Time elapsed: 0.113 s
% 0.19/0.51  % (8226)------------------------------
% 0.19/0.51  % (8226)------------------------------
% 4.27/0.92  % (8216)Time limit reached!
% 4.27/0.92  % (8216)------------------------------
% 4.27/0.92  % (8216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.65/0.93  % (8216)Termination reason: Time limit
% 4.65/0.93  % (8216)Termination phase: Saturation
% 4.65/0.93  
% 4.65/0.93  % (8216)Memory used [KB]: 12665
% 4.65/0.93  % (8216)Time elapsed: 0.500 s
% 4.65/0.93  % (8216)------------------------------
% 4.65/0.93  % (8216)------------------------------
% 4.82/1.00  % (8219)Time limit reached!
% 4.82/1.00  % (8219)------------------------------
% 4.82/1.00  % (8219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.82/1.00  % (8219)Termination reason: Time limit
% 4.82/1.00  % (8219)Termination phase: Saturation
% 4.82/1.00  
% 4.82/1.00  % (8219)Memory used [KB]: 20468
% 4.82/1.00  % (8219)Time elapsed: 0.600 s
% 4.82/1.00  % (8219)------------------------------
% 4.82/1.00  % (8219)------------------------------
% 5.39/1.05  % (8230)Refutation found. Thanks to Tanya!
% 5.39/1.05  % SZS status Theorem for theBenchmark
% 5.39/1.05  % SZS output start Proof for theBenchmark
% 5.39/1.05  fof(f20801,plain,(
% 5.39/1.05    $false),
% 5.39/1.05    inference(avatar_sat_refutation,[],[f1759,f5256,f8310,f8476,f15194,f20800])).
% 5.39/1.05  fof(f20800,plain,(
% 5.39/1.05    ~spl4_9 | spl4_10 | ~spl4_93),
% 5.39/1.05    inference(avatar_contradiction_clause,[],[f20799])).
% 5.39/1.05  fof(f20799,plain,(
% 5.39/1.05    $false | (~spl4_9 | spl4_10 | ~spl4_93)),
% 5.39/1.05    inference(subsumption_resolution,[],[f20798,f20406])).
% 5.39/1.05  fof(f20406,plain,(
% 5.39/1.05    ( ! [X6,X5] : (r1_tarski(k3_xboole_0(X5,X6),X5)) ) | ~spl4_93),
% 5.39/1.05    inference(superposition,[],[f20375,f43])).
% 5.39/1.05  fof(f43,plain,(
% 5.39/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 5.39/1.05    inference(cnf_transformation,[],[f10])).
% 5.39/1.05  fof(f10,axiom,(
% 5.39/1.05    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 5.39/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 5.39/1.05  fof(f20375,plain,(
% 5.39/1.05    ( ! [X180,X179] : (r1_tarski(X179,k2_xboole_0(X180,X179))) ) | ~spl4_93),
% 5.39/1.05    inference(trivial_inequality_removal,[],[f20298])).
% 5.39/1.05  fof(f20298,plain,(
% 5.39/1.05    ( ! [X180,X179] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X179,k2_xboole_0(X180,X179))) ) | ~spl4_93),
% 5.39/1.05    inference(superposition,[],[f37,f19040])).
% 5.39/1.05  fof(f19040,plain,(
% 5.39/1.05    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,X8))) ) | ~spl4_93),
% 5.39/1.05    inference(forward_demodulation,[],[f18748,f41])).
% 5.39/1.05  fof(f41,plain,(
% 5.39/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.39/1.05    inference(cnf_transformation,[],[f13])).
% 5.39/1.05  fof(f13,axiom,(
% 5.39/1.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.39/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 5.39/1.05  fof(f18748,plain,(
% 5.39/1.05    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9)))) ) | ~spl4_93),
% 5.39/1.05    inference(superposition,[],[f18734,f36])).
% 5.39/1.05  fof(f36,plain,(
% 5.39/1.05    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.39/1.05    inference(cnf_transformation,[],[f15])).
% 5.39/1.05  fof(f15,axiom,(
% 5.39/1.05    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.39/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 5.39/1.05  fof(f18734,plain,(
% 5.39/1.05    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) ) | ~spl4_93),
% 5.39/1.05    inference(subsumption_resolution,[],[f18731,f5398])).
% 5.39/1.05  fof(f5398,plain,(
% 5.39/1.05    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_93),
% 5.39/1.05    inference(duplicate_literal_removal,[],[f5396])).
% 5.39/1.05  fof(f5396,plain,(
% 5.39/1.05    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_93),
% 5.39/1.05    inference(resolution,[],[f5395,f59])).
% 5.39/1.05  fof(f59,plain,(
% 5.39/1.05    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 5.39/1.05    inference(cnf_transformation,[],[f33])).
% 5.39/1.05  fof(f33,plain,(
% 5.39/1.05    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 5.39/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f32])).
% 5.39/1.05  fof(f32,plain,(
% 5.39/1.05    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 5.39/1.05    introduced(choice_axiom,[])).
% 5.39/1.05  fof(f22,plain,(
% 5.39/1.05    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 5.39/1.05    inference(ennf_transformation,[],[f19])).
% 5.39/1.05  fof(f19,plain,(
% 5.39/1.05    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 5.39/1.05    inference(rectify,[],[f5])).
% 5.39/1.05  fof(f5,axiom,(
% 5.39/1.05    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 5.39/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 5.39/1.05  fof(f5395,plain,(
% 5.39/1.05    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_93),
% 5.39/1.05    inference(trivial_inequality_removal,[],[f5394])).
% 5.39/1.05  fof(f5394,plain,(
% 5.39/1.05    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_93),
% 5.39/1.05    inference(superposition,[],[f56,f5366])).
% 5.39/1.05  fof(f5366,plain,(
% 5.39/1.05    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_93),
% 5.39/1.05    inference(resolution,[],[f5354,f39])).
% 5.39/1.05  fof(f39,plain,(
% 5.39/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 5.39/1.05    inference(cnf_transformation,[],[f21])).
% 5.39/1.05  fof(f21,plain,(
% 5.39/1.05    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 5.39/1.05    inference(ennf_transformation,[],[f11])).
% 5.39/1.05  fof(f11,axiom,(
% 5.39/1.05    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 5.39/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 5.39/1.05  fof(f5354,plain,(
% 5.39/1.05    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl4_93),
% 5.39/1.05    inference(superposition,[],[f54,f5270])).
% 5.39/1.05  fof(f5270,plain,(
% 5.39/1.05    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) | ~spl4_93),
% 5.39/1.05    inference(forward_demodulation,[],[f5262,f46])).
% 5.39/1.05  fof(f46,plain,(
% 5.39/1.05    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.39/1.05    inference(cnf_transformation,[],[f14])).
% 5.39/1.05  fof(f14,axiom,(
% 5.39/1.05    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 5.39/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 5.39/1.05  fof(f5262,plain,(
% 5.39/1.05    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,sK0) | ~spl4_93),
% 5.39/1.05    inference(superposition,[],[f40,f5157])).
% 5.39/1.05  fof(f5157,plain,(
% 5.39/1.05    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) | ~spl4_93),
% 5.39/1.05    inference(avatar_component_clause,[],[f5156])).
% 5.39/1.05  fof(f5156,plain,(
% 5.39/1.05    spl4_93 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)),
% 5.39/1.05    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).
% 5.39/1.05  fof(f40,plain,(
% 5.39/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.39/1.05    inference(cnf_transformation,[],[f16])).
% 5.39/1.05  fof(f16,axiom,(
% 5.39/1.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.39/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 5.39/1.05  fof(f54,plain,(
% 5.39/1.05    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 5.39/1.05    inference(cnf_transformation,[],[f12])).
% 5.39/1.05  fof(f12,axiom,(
% 5.39/1.05    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 5.39/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 5.39/1.05  fof(f56,plain,(
% 5.39/1.05    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 5.39/1.05    inference(cnf_transformation,[],[f31])).
% 5.39/1.05  fof(f31,plain,(
% 5.39/1.05    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 5.39/1.05    inference(nnf_transformation,[],[f4])).
% 5.39/1.05  fof(f4,axiom,(
% 5.39/1.05    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 5.39/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 5.39/1.05  fof(f18731,plain,(
% 5.39/1.05    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3) | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0)) ) | ~spl4_93),
% 5.39/1.05    inference(duplicate_literal_removal,[],[f18670])).
% 5.39/1.05  fof(f18670,plain,(
% 5.39/1.05    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3) | k1_xboole_0 = k4_xboole_0(X3,X3) | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0)) ) | ~spl4_93),
% 5.39/1.05    inference(resolution,[],[f5400,f52])).
% 5.39/1.05  fof(f52,plain,(
% 5.39/1.05    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 5.39/1.05    inference(cnf_transformation,[],[f30])).
% 5.39/1.05  fof(f30,plain,(
% 5.39/1.05    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.39/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 5.39/1.05  fof(f29,plain,(
% 5.39/1.05    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 5.39/1.05    introduced(choice_axiom,[])).
% 5.39/1.05  fof(f28,plain,(
% 5.39/1.05    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.39/1.05    inference(rectify,[],[f27])).
% 5.39/1.05  fof(f27,plain,(
% 5.39/1.05    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.39/1.05    inference(flattening,[],[f26])).
% 5.39/1.05  fof(f26,plain,(
% 5.39/1.05    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.39/1.05    inference(nnf_transformation,[],[f3])).
% 5.39/1.05  fof(f3,axiom,(
% 5.39/1.05    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 5.39/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 5.39/1.05  fof(f5400,plain,(
% 5.39/1.05    ( ! [X2,X3] : (r2_hidden(sK2(X2,X3,k1_xboole_0),X2) | k1_xboole_0 = k4_xboole_0(X2,X3)) ) | ~spl4_93),
% 5.39/1.05    inference(resolution,[],[f5398,f51])).
% 5.39/1.05  fof(f51,plain,(
% 5.39/1.05    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 5.39/1.05    inference(cnf_transformation,[],[f30])).
% 5.39/1.05  fof(f37,plain,(
% 5.39/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 5.39/1.05    inference(cnf_transformation,[],[f25])).
% 5.39/1.05  fof(f25,plain,(
% 5.39/1.05    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 5.39/1.05    inference(nnf_transformation,[],[f6])).
% 5.39/1.05  fof(f6,axiom,(
% 5.39/1.05    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 5.39/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 5.39/1.05  fof(f20798,plain,(
% 5.39/1.05    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl4_9 | spl4_10 | ~spl4_93)),
% 5.39/1.05    inference(subsumption_resolution,[],[f4568,f5398])).
% 5.39/1.05  fof(f4568,plain,(
% 5.39/1.05    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl4_9 | spl4_10)),
% 5.39/1.05    inference(superposition,[],[f2474,f38])).
% 5.39/1.05  fof(f38,plain,(
% 5.39/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 5.39/1.05    inference(cnf_transformation,[],[f25])).
% 5.39/1.05  fof(f2474,plain,(
% 5.39/1.05    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) | (~spl4_9 | spl4_10)),
% 5.39/1.05    inference(resolution,[],[f647,f170])).
% 5.39/1.05  fof(f170,plain,(
% 5.39/1.05    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl4_9),
% 5.39/1.05    inference(avatar_component_clause,[],[f168])).
% 5.39/1.05  fof(f168,plain,(
% 5.39/1.05    spl4_9 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 5.39/1.05    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 5.39/1.05  fof(f647,plain,(
% 5.39/1.05    ( ! [X1] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,sK0))) ) | spl4_10),
% 5.39/1.05    inference(resolution,[],[f173,f60])).
% 5.39/1.05  fof(f60,plain,(
% 5.39/1.05    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 5.39/1.05    inference(equality_resolution,[],[f50])).
% 5.39/1.05  fof(f50,plain,(
% 5.39/1.05    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 5.39/1.05    inference(cnf_transformation,[],[f30])).
% 5.39/1.05  fof(f173,plain,(
% 5.39/1.05    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | spl4_10),
% 5.39/1.05    inference(avatar_component_clause,[],[f172])).
% 5.39/1.05  fof(f172,plain,(
% 5.39/1.05    spl4_10 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 5.39/1.05    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 5.39/1.05  fof(f15194,plain,(
% 5.39/1.05    spl4_9 | spl4_10),
% 5.39/1.05    inference(avatar_split_clause,[],[f15193,f172,f168])).
% 5.39/1.05  fof(f15193,plain,(
% 5.39/1.05    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 5.39/1.05    inference(equality_resolution,[],[f67])).
% 5.39/1.05  fof(f67,plain,(
% 5.39/1.05    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 5.39/1.05    inference(superposition,[],[f34,f51])).
% 5.39/1.05  fof(f34,plain,(
% 5.39/1.05    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 5.39/1.05    inference(cnf_transformation,[],[f24])).
% 5.39/1.05  fof(f24,plain,(
% 5.39/1.05    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 5.39/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).
% 5.39/1.05  fof(f23,plain,(
% 5.39/1.05    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 5.39/1.05    introduced(choice_axiom,[])).
% 5.39/1.05  fof(f20,plain,(
% 5.39/1.05    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.39/1.05    inference(ennf_transformation,[],[f18])).
% 5.39/1.05  fof(f18,negated_conjecture,(
% 5.39/1.05    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.39/1.05    inference(negated_conjecture,[],[f17])).
% 5.39/1.05  fof(f17,conjecture,(
% 5.39/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.39/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.39/1.05  fof(f8476,plain,(
% 5.39/1.05    ~spl4_10 | spl4_17 | ~spl4_9),
% 5.39/1.05    inference(avatar_split_clause,[],[f639,f168,f641,f172])).
% 5.39/1.05  fof(f641,plain,(
% 5.39/1.05    spl4_17 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 5.39/1.05    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 5.39/1.05  fof(f639,plain,(
% 5.39/1.05    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl4_9),
% 5.39/1.05    inference(subsumption_resolution,[],[f628,f34])).
% 5.39/1.05  fof(f628,plain,(
% 5.39/1.05    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl4_9),
% 5.39/1.05    inference(resolution,[],[f170,f53])).
% 5.39/1.05  fof(f53,plain,(
% 5.39/1.05    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 5.39/1.05    inference(cnf_transformation,[],[f30])).
% 5.39/1.05  fof(f8310,plain,(
% 5.39/1.05    spl4_9 | ~spl4_10),
% 5.39/1.05    inference(avatar_contradiction_clause,[],[f8309])).
% 5.39/1.05  fof(f8309,plain,(
% 5.39/1.05    $false | (spl4_9 | ~spl4_10)),
% 5.39/1.05    inference(subsumption_resolution,[],[f8308,f7611])).
% 5.39/1.05  fof(f7611,plain,(
% 5.39/1.05    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl4_9),
% 5.39/1.05    inference(subsumption_resolution,[],[f7602,f34])).
% 5.39/1.05  fof(f7602,plain,(
% 5.39/1.05    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl4_9),
% 5.39/1.05    inference(resolution,[],[f169,f52])).
% 5.39/1.05  fof(f169,plain,(
% 5.39/1.05    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl4_9),
% 5.39/1.05    inference(avatar_component_clause,[],[f168])).
% 5.39/1.05  fof(f8308,plain,(
% 5.39/1.05    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (spl4_9 | ~spl4_10)),
% 5.39/1.05    inference(forward_demodulation,[],[f8289,f40])).
% 5.39/1.05  fof(f8289,plain,(
% 5.39/1.05    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | (spl4_9 | ~spl4_10)),
% 5.39/1.05    inference(resolution,[],[f7604,f174])).
% 5.39/1.05  fof(f174,plain,(
% 5.39/1.05    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl4_10),
% 5.39/1.05    inference(avatar_component_clause,[],[f172])).
% 5.39/1.05  fof(f7604,plain,(
% 5.39/1.05    ( ! [X1] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1)))) ) | spl4_9),
% 5.39/1.05    inference(resolution,[],[f169,f60])).
% 5.39/1.05  fof(f5256,plain,(
% 5.39/1.05    spl4_93),
% 5.39/1.05    inference(avatar_contradiction_clause,[],[f5255])).
% 5.39/1.05  fof(f5255,plain,(
% 5.39/1.05    $false | spl4_93),
% 5.39/1.05    inference(subsumption_resolution,[],[f5247,f5164])).
% 5.39/1.05  fof(f5164,plain,(
% 5.39/1.05    ~r1_xboole_0(k1_xboole_0,sK0) | spl4_93),
% 5.39/1.05    inference(trivial_inequality_removal,[],[f5161])).
% 5.39/1.05  fof(f5161,plain,(
% 5.39/1.05    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,sK0) | spl4_93),
% 5.39/1.05    inference(superposition,[],[f5158,f55])).
% 5.39/1.05  fof(f55,plain,(
% 5.39/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 5.39/1.05    inference(cnf_transformation,[],[f31])).
% 5.39/1.05  fof(f5158,plain,(
% 5.39/1.05    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK0) | spl4_93),
% 5.39/1.05    inference(avatar_component_clause,[],[f5156])).
% 5.39/1.05  fof(f5247,plain,(
% 5.39/1.05    r1_xboole_0(k1_xboole_0,sK0) | spl4_93),
% 5.39/1.05    inference(resolution,[],[f5207,f57])).
% 5.39/1.05  fof(f57,plain,(
% 5.39/1.05    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 5.39/1.05    inference(cnf_transformation,[],[f33])).
% 5.39/1.05  fof(f5207,plain,(
% 5.39/1.05    ( ! [X2] : (~r2_hidden(sK3(k1_xboole_0,sK0),X2)) ) | spl4_93),
% 5.39/1.05    inference(forward_demodulation,[],[f5205,f46])).
% 5.39/1.05  fof(f5205,plain,(
% 5.39/1.05    ( ! [X2] : (~r2_hidden(sK3(k1_xboole_0,sK0),k4_xboole_0(X2,k1_xboole_0))) ) | spl4_93),
% 5.39/1.05    inference(resolution,[],[f5185,f61])).
% 5.39/1.05  fof(f61,plain,(
% 5.39/1.05    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 5.39/1.05    inference(equality_resolution,[],[f49])).
% 5.39/1.05  fof(f49,plain,(
% 5.39/1.05    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 5.39/1.05    inference(cnf_transformation,[],[f30])).
% 5.39/1.05  fof(f5185,plain,(
% 5.39/1.05    r2_hidden(sK3(k1_xboole_0,sK0),k1_xboole_0) | spl4_93),
% 5.39/1.05    inference(resolution,[],[f5164,f57])).
% 5.39/1.05  fof(f1759,plain,(
% 5.39/1.05    ~spl4_9 | ~spl4_17),
% 5.39/1.05    inference(avatar_contradiction_clause,[],[f1758])).
% 5.39/1.05  fof(f1758,plain,(
% 5.39/1.05    $false | (~spl4_9 | ~spl4_17)),
% 5.39/1.05    inference(subsumption_resolution,[],[f1752,f643])).
% 5.39/1.05  fof(f643,plain,(
% 5.39/1.05    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl4_17),
% 5.39/1.05    inference(avatar_component_clause,[],[f641])).
% 5.39/1.05  fof(f1752,plain,(
% 5.39/1.05    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl4_9),
% 5.39/1.05    inference(superposition,[],[f631,f40])).
% 5.39/1.05  fof(f631,plain,(
% 5.39/1.05    ( ! [X2] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X2,k3_xboole_0(sK0,sK1)))) ) | ~spl4_9),
% 5.39/1.05    inference(resolution,[],[f170,f61])).
% 5.39/1.05  % SZS output end Proof for theBenchmark
% 5.39/1.05  % (8230)------------------------------
% 5.39/1.05  % (8230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.39/1.05  % (8230)Termination reason: Refutation
% 5.39/1.05  
% 5.39/1.05  % (8230)Memory used [KB]: 13688
% 5.39/1.05  % (8230)Time elapsed: 0.650 s
% 5.39/1.05  % (8230)------------------------------
% 5.39/1.05  % (8230)------------------------------
% 5.39/1.05  % (8210)Success in time 0.699 s
%------------------------------------------------------------------------------
