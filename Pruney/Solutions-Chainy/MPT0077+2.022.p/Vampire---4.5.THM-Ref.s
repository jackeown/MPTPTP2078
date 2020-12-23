%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 148 expanded)
%              Number of leaves         :   12 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  241 ( 543 expanded)
%              Number of equality atoms :   27 (  66 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f458,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f56,f150,f371,f455])).

fof(f455,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f444,f155])).

fof(f155,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f54,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f54,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f444,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | ~ spl5_1
    | spl5_2 ),
    inference(superposition,[],[f387,f412])).

fof(f412,plain,
    ( ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k2_xboole_0(X0,sK2))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f406,f38])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f406,plain,
    ( ! [X0] : k2_xboole_0(k3_xboole_0(sK0,X0),k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(X0,sK2))
    | ~ spl5_1 ),
    inference(superposition,[],[f37,f385])).

fof(f385,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f45,f27])).

fof(f45,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f387,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl5_2 ),
    inference(resolution,[],[f48,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f371,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f368,f81])).

fof(f81,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f59,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f49,f27])).

fof(f49,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f59,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl5_2 ),
    inference(resolution,[],[f49,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f368,plain,
    ( r2_hidden(sK3(sK0,sK2),k1_xboole_0)
    | spl5_1
    | ~ spl5_2 ),
    inference(superposition,[],[f336,f60])).

fof(f336,plain,
    ( ! [X6] : r2_hidden(sK3(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(X6,sK2)))
    | spl5_1 ),
    inference(superposition,[],[f175,f37])).

fof(f175,plain,
    ( ! [X1] : r2_hidden(sK3(sK0,sK2),k2_xboole_0(X1,k3_xboole_0(sK0,sK2)))
    | spl5_1 ),
    inference(resolution,[],[f152,f39])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f152,plain,
    ( r2_hidden(sK3(sK0,sK2),k3_xboole_0(sK0,sK2))
    | spl5_1 ),
    inference(resolution,[],[f44,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f150,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f147,f81])).

fof(f147,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | ~ spl5_2
    | spl5_3 ),
    inference(superposition,[],[f120,f60])).

fof(f120,plain,
    ( ! [X0] : r2_hidden(sK3(sK0,sK1),k3_xboole_0(sK0,k2_xboole_0(sK1,X0)))
    | spl5_3 ),
    inference(superposition,[],[f67,f37])).

fof(f67,plain,
    ( ! [X0] : r2_hidden(sK3(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK1),X0))
    | spl5_3 ),
    inference(resolution,[],[f57,f40])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,
    ( r2_hidden(sK3(sK0,sK1),k3_xboole_0(sK0,sK1))
    | spl5_3 ),
    inference(resolution,[],[f53,f29])).

fof(f53,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f56,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f21,f43,f52,f47])).

fof(f21,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f55,plain,
    ( spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f25,f47,f52])).

fof(f25,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f26,f47,f43])).

fof(f26,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:00:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (26107)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.45  % (26107)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f458,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f50,f55,f56,f150,f371,f455])).
% 0.22/0.45  fof(f455,plain,(
% 0.22/0.45    ~spl5_1 | spl5_2 | ~spl5_3),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f454])).
% 0.22/0.45  fof(f454,plain,(
% 0.22/0.45    $false | (~spl5_1 | spl5_2 | ~spl5_3)),
% 0.22/0.45    inference(subsumption_resolution,[],[f444,f155])).
% 0.22/0.45  fof(f155,plain,(
% 0.22/0.45    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl5_3),
% 0.22/0.45    inference(resolution,[],[f54,f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.46    inference(nnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    r1_xboole_0(sK0,sK1) | ~spl5_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f52])).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    spl5_3 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.46  fof(f444,plain,(
% 0.22/0.46    k1_xboole_0 != k3_xboole_0(sK0,sK1) | (~spl5_1 | spl5_2)),
% 0.22/0.46    inference(superposition,[],[f387,f412])).
% 0.22/0.46  fof(f412,plain,(
% 0.22/0.46    ( ! [X0] : (k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k2_xboole_0(X0,sK2))) ) | ~spl5_1),
% 0.22/0.46    inference(forward_demodulation,[],[f406,f38])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.46  fof(f406,plain,(
% 0.22/0.46    ( ! [X0] : (k2_xboole_0(k3_xboole_0(sK0,X0),k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(X0,sK2))) ) | ~spl5_1),
% 0.22/0.46    inference(superposition,[],[f37,f385])).
% 0.22/0.46  fof(f385,plain,(
% 0.22/0.46    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl5_1),
% 0.22/0.46    inference(resolution,[],[f45,f27])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    r1_xboole_0(sK0,sK2) | ~spl5_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f43])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    spl5_1 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.22/0.46  fof(f387,plain,(
% 0.22/0.46    k1_xboole_0 != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl5_2),
% 0.22/0.46    inference(resolution,[],[f48,f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl5_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f47])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    spl5_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.46  fof(f371,plain,(
% 0.22/0.46    spl5_1 | ~spl5_2),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f370])).
% 0.22/0.46  fof(f370,plain,(
% 0.22/0.46    $false | (spl5_1 | ~spl5_2)),
% 0.22/0.46    inference(subsumption_resolution,[],[f368,f81])).
% 0.22/0.46  fof(f81,plain,(
% 0.22/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_2),
% 0.22/0.46    inference(backward_demodulation,[],[f59,f60])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_2),
% 0.22/0.46    inference(resolution,[],[f49,f27])).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f47])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)))) ) | ~spl5_2),
% 0.22/0.46    inference(resolution,[],[f49,f30])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,plain,(
% 0.22/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.46    inference(rectify,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.46  fof(f368,plain,(
% 0.22/0.46    r2_hidden(sK3(sK0,sK2),k1_xboole_0) | (spl5_1 | ~spl5_2)),
% 0.22/0.46    inference(superposition,[],[f336,f60])).
% 0.22/0.46  fof(f336,plain,(
% 0.22/0.46    ( ! [X6] : (r2_hidden(sK3(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(X6,sK2)))) ) | spl5_1),
% 0.22/0.46    inference(superposition,[],[f175,f37])).
% 0.22/0.46  fof(f175,plain,(
% 0.22/0.46    ( ! [X1] : (r2_hidden(sK3(sK0,sK2),k2_xboole_0(X1,k3_xboole_0(sK0,sK2)))) ) | spl5_1),
% 0.22/0.46    inference(resolution,[],[f152,f39])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.22/0.46    inference(equality_resolution,[],[f33])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.46    inference(rectify,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.46    inference(flattening,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.46    inference(nnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.46  fof(f152,plain,(
% 0.22/0.46    r2_hidden(sK3(sK0,sK2),k3_xboole_0(sK0,sK2)) | spl5_1),
% 0.22/0.46    inference(resolution,[],[f44,f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    ~r1_xboole_0(sK0,sK2) | spl5_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f43])).
% 0.22/0.46  fof(f150,plain,(
% 0.22/0.46    ~spl5_2 | spl5_3),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f149])).
% 0.22/0.46  fof(f149,plain,(
% 0.22/0.46    $false | (~spl5_2 | spl5_3)),
% 0.22/0.46    inference(subsumption_resolution,[],[f147,f81])).
% 0.22/0.46  fof(f147,plain,(
% 0.22/0.46    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | (~spl5_2 | spl5_3)),
% 0.22/0.46    inference(superposition,[],[f120,f60])).
% 0.22/0.46  fof(f120,plain,(
% 0.22/0.46    ( ! [X0] : (r2_hidden(sK3(sK0,sK1),k3_xboole_0(sK0,k2_xboole_0(sK1,X0)))) ) | spl5_3),
% 0.22/0.46    inference(superposition,[],[f67,f37])).
% 0.22/0.46  fof(f67,plain,(
% 0.22/0.46    ( ! [X0] : (r2_hidden(sK3(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK1),X0))) ) | spl5_3),
% 0.22/0.46    inference(resolution,[],[f57,f40])).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.22/0.46    inference(equality_resolution,[],[f32])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    r2_hidden(sK3(sK0,sK1),k3_xboole_0(sK0,sK1)) | spl5_3),
% 0.22/0.46    inference(resolution,[],[f53,f29])).
% 0.22/0.46  fof(f53,plain,(
% 0.22/0.46    ~r1_xboole_0(sK0,sK1) | spl5_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f52])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    ~spl5_2 | ~spl5_3 | ~spl5_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f21,f43,f52,f47])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.46    inference(cnf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.46    inference(ennf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.46    inference(negated_conjecture,[],[f6])).
% 0.22/0.46  fof(f6,conjecture,(
% 0.22/0.46    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.22/0.46  fof(f55,plain,(
% 0.22/0.46    spl5_3 | spl5_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f25,f47,f52])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f12])).
% 0.22/0.46  fof(f50,plain,(
% 0.22/0.46    spl5_1 | spl5_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f26,f47,f43])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 0.22/0.46    inference(cnf_transformation,[],[f12])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (26107)------------------------------
% 0.22/0.46  % (26107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (26107)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (26107)Memory used [KB]: 6268
% 0.22/0.46  % (26107)Time elapsed: 0.038 s
% 0.22/0.46  % (26107)------------------------------
% 0.22/0.46  % (26107)------------------------------
% 0.22/0.46  % (26087)Success in time 0.091 s
%------------------------------------------------------------------------------
