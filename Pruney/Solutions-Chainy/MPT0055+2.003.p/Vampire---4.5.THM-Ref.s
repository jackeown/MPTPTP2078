%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:04 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 115 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  208 ( 546 expanded)
%              Number of equality atoms :   26 (  78 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f901,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f179,f197,f299,f881,f886,f900])).

fof(f900,plain,
    ( spl6_10
    | ~ spl6_11
    | spl6_12 ),
    inference(avatar_contradiction_clause,[],[f899])).

fof(f899,plain,
    ( $false
    | spl6_10
    | ~ spl6_11
    | spl6_12 ),
    inference(subsumption_resolution,[],[f898,f195])).

fof(f195,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl6_12
  <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f898,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl6_10
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f890,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f890,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl6_10
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f178,f173,f68])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f173,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl6_10
  <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f178,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl6_11
  <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f886,plain,
    ( ~ spl6_12
    | spl6_10 ),
    inference(avatar_split_clause,[],[f885,f172,f194])).

fof(f885,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl6_10 ),
    inference(subsumption_resolution,[],[f180,f173])).

fof(f180,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1))
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f41,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f41,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f25])).

fof(f25,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f881,plain,
    ( ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f880])).

fof(f880,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f870,f196])).

fof(f196,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f194])).

fof(f870,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_10 ),
    inference(superposition,[],[f283,f48])).

fof(f283,plain,
    ( ! [X0] : ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f174,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f174,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f172])).

fof(f299,plain,
    ( spl6_11
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f285,f172,f176])).

fof(f285,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f43,f174,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f197,plain,
    ( ~ spl6_11
    | spl6_12
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f192,f172,f194,f176])).

fof(f192,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f191,f174])).

fof(f191,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2] :
      ( k3_xboole_0(sK0,sK1) != X2
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),sK0)
      | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),X2) ) ),
    inference(superposition,[],[f41,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f179,plain,
    ( spl6_10
    | spl6_11 ),
    inference(avatar_split_clause,[],[f170,f176,f172])).

fof(f170,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f41,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (18443)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (18447)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (18459)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (18448)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (18443)Refutation not found, incomplete strategy% (18443)------------------------------
% 0.20/0.52  % (18443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18443)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (18443)Memory used [KB]: 10618
% 0.20/0.52  % (18443)Time elapsed: 0.112 s
% 0.20/0.52  % (18443)------------------------------
% 0.20/0.52  % (18443)------------------------------
% 0.20/0.52  % (18457)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (18451)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (18464)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (18456)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (18444)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (18455)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (18463)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (18446)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (18442)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (18463)Refutation not found, incomplete strategy% (18463)------------------------------
% 0.20/0.54  % (18463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (18452)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (18463)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (18463)Memory used [KB]: 10746
% 0.20/0.54  % (18463)Time elapsed: 0.118 s
% 0.20/0.54  % (18463)------------------------------
% 0.20/0.54  % (18463)------------------------------
% 0.20/0.54  % (18468)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (18441)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.55  % (18465)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (18441)Refutation not found, incomplete strategy% (18441)------------------------------
% 0.20/0.55  % (18441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (18441)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (18441)Memory used [KB]: 1663
% 0.20/0.55  % (18441)Time elapsed: 0.135 s
% 0.20/0.55  % (18441)------------------------------
% 0.20/0.55  % (18441)------------------------------
% 0.20/0.55  % (18445)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (18450)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (18460)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (18458)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (18458)Refutation not found, incomplete strategy% (18458)------------------------------
% 0.20/0.55  % (18458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (18458)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (18458)Memory used [KB]: 10618
% 0.20/0.55  % (18458)Time elapsed: 0.148 s
% 0.20/0.55  % (18458)------------------------------
% 0.20/0.55  % (18458)------------------------------
% 0.20/0.56  % (18454)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.56  % (18466)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (18470)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (18462)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (18462)Refutation not found, incomplete strategy% (18462)------------------------------
% 0.20/0.56  % (18462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (18461)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.57  % (18462)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (18462)Memory used [KB]: 1663
% 0.20/0.57  % (18462)Time elapsed: 0.128 s
% 0.20/0.57  % (18462)------------------------------
% 0.20/0.57  % (18462)------------------------------
% 0.20/0.57  % (18449)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.57  % (18467)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.57  % (18469)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.57  % (18449)Refutation not found, incomplete strategy% (18449)------------------------------
% 0.20/0.57  % (18449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (18449)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (18449)Memory used [KB]: 10618
% 0.20/0.57  % (18449)Time elapsed: 0.144 s
% 0.20/0.57  % (18449)------------------------------
% 0.20/0.57  % (18449)------------------------------
% 0.20/0.58  % (18453)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.59  % (18461)Refutation not found, incomplete strategy% (18461)------------------------------
% 0.20/0.59  % (18461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (18461)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (18461)Memory used [KB]: 10746
% 0.20/0.59  % (18461)Time elapsed: 0.180 s
% 0.20/0.59  % (18461)------------------------------
% 0.20/0.59  % (18461)------------------------------
% 1.89/0.64  % (18471)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.11/0.65  % (18471)Refutation not found, incomplete strategy% (18471)------------------------------
% 2.11/0.65  % (18471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.65  % (18471)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.65  
% 2.11/0.65  % (18471)Memory used [KB]: 6140
% 2.11/0.65  % (18471)Time elapsed: 0.084 s
% 2.11/0.65  % (18471)------------------------------
% 2.11/0.65  % (18471)------------------------------
% 2.11/0.67  % (18467)Refutation found. Thanks to Tanya!
% 2.11/0.67  % SZS status Theorem for theBenchmark
% 2.11/0.67  % SZS output start Proof for theBenchmark
% 2.11/0.67  fof(f901,plain,(
% 2.11/0.67    $false),
% 2.11/0.67    inference(avatar_sat_refutation,[],[f179,f197,f299,f881,f886,f900])).
% 2.11/0.67  fof(f900,plain,(
% 2.11/0.67    spl6_10 | ~spl6_11 | spl6_12),
% 2.11/0.67    inference(avatar_contradiction_clause,[],[f899])).
% 2.11/0.67  fof(f899,plain,(
% 2.11/0.67    $false | (spl6_10 | ~spl6_11 | spl6_12)),
% 2.11/0.67    inference(subsumption_resolution,[],[f898,f195])).
% 2.11/0.67  fof(f195,plain,(
% 2.11/0.67    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl6_12),
% 2.11/0.67    inference(avatar_component_clause,[],[f194])).
% 2.11/0.67  fof(f194,plain,(
% 2.11/0.67    spl6_12 <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.11/0.67  fof(f898,plain,(
% 2.11/0.67    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (spl6_10 | ~spl6_11)),
% 2.11/0.67    inference(forward_demodulation,[],[f890,f48])).
% 2.11/0.67  fof(f48,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.11/0.67    inference(cnf_transformation,[],[f15])).
% 2.11/0.67  fof(f15,axiom,(
% 2.11/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.11/0.67  fof(f890,plain,(
% 2.11/0.67    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | (spl6_10 | ~spl6_11)),
% 2.11/0.67    inference(unit_resulting_resolution,[],[f178,f173,f68])).
% 2.11/0.67  fof(f68,plain,(
% 2.11/0.67    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.11/0.67    inference(equality_resolution,[],[f64])).
% 2.11/0.67  fof(f64,plain,(
% 2.11/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.11/0.67    inference(cnf_transformation,[],[f40])).
% 2.11/0.67  fof(f40,plain,(
% 2.11/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.11/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 2.11/0.67  fof(f39,plain,(
% 2.11/0.67    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f38,plain,(
% 2.11/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.11/0.67    inference(rectify,[],[f37])).
% 2.11/0.67  fof(f37,plain,(
% 2.11/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.11/0.67    inference(flattening,[],[f36])).
% 2.11/0.67  fof(f36,plain,(
% 2.11/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.11/0.67    inference(nnf_transformation,[],[f4])).
% 2.11/0.67  fof(f4,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.11/0.67  fof(f173,plain,(
% 2.11/0.67    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl6_10),
% 2.11/0.67    inference(avatar_component_clause,[],[f172])).
% 2.11/0.67  fof(f172,plain,(
% 2.11/0.67    spl6_10 <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.11/0.67  fof(f178,plain,(
% 2.11/0.67    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl6_11),
% 2.11/0.67    inference(avatar_component_clause,[],[f176])).
% 2.11/0.67  fof(f176,plain,(
% 2.11/0.67    spl6_11 <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.11/0.67  fof(f886,plain,(
% 2.11/0.67    ~spl6_12 | spl6_10),
% 2.11/0.67    inference(avatar_split_clause,[],[f885,f172,f194])).
% 2.11/0.67  fof(f885,plain,(
% 2.11/0.67    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl6_10),
% 2.11/0.67    inference(subsumption_resolution,[],[f180,f173])).
% 2.11/0.67  fof(f180,plain,(
% 2.11/0.67    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.11/0.67    inference(equality_resolution,[],[f78])).
% 2.11/0.67  fof(f78,plain,(
% 2.11/0.67    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 2.11/0.67    inference(superposition,[],[f41,f66])).
% 2.11/0.67  fof(f66,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f40])).
% 2.11/0.67  fof(f41,plain,(
% 2.11/0.67    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.11/0.67    inference(cnf_transformation,[],[f26])).
% 2.11/0.67  fof(f26,plain,(
% 2.11/0.67    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.11/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f25])).
% 2.11/0.67  fof(f25,plain,(
% 2.11/0.67    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f20,plain,(
% 2.11/0.67    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.11/0.67    inference(ennf_transformation,[],[f17])).
% 2.11/0.67  fof(f17,negated_conjecture,(
% 2.11/0.67    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.11/0.67    inference(negated_conjecture,[],[f16])).
% 2.11/0.67  fof(f16,conjecture,(
% 2.11/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.11/0.67  fof(f881,plain,(
% 2.11/0.67    ~spl6_10 | ~spl6_12),
% 2.11/0.67    inference(avatar_contradiction_clause,[],[f880])).
% 2.11/0.67  fof(f880,plain,(
% 2.11/0.67    $false | (~spl6_10 | ~spl6_12)),
% 2.11/0.67    inference(subsumption_resolution,[],[f870,f196])).
% 2.11/0.67  fof(f196,plain,(
% 2.11/0.67    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl6_12),
% 2.11/0.67    inference(avatar_component_clause,[],[f194])).
% 2.11/0.67  fof(f870,plain,(
% 2.11/0.67    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl6_10),
% 2.11/0.67    inference(superposition,[],[f283,f48])).
% 2.11/0.67  fof(f283,plain,(
% 2.11/0.67    ( ! [X0] : (~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))) ) | ~spl6_10),
% 2.11/0.67    inference(unit_resulting_resolution,[],[f174,f69])).
% 2.11/0.67  fof(f69,plain,(
% 2.11/0.67    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.11/0.67    inference(equality_resolution,[],[f63])).
% 2.11/0.67  fof(f63,plain,(
% 2.11/0.67    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.11/0.67    inference(cnf_transformation,[],[f40])).
% 2.11/0.67  fof(f174,plain,(
% 2.11/0.67    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl6_10),
% 2.11/0.67    inference(avatar_component_clause,[],[f172])).
% 2.11/0.67  fof(f299,plain,(
% 2.11/0.67    spl6_11 | ~spl6_10),
% 2.11/0.67    inference(avatar_split_clause,[],[f285,f172,f176])).
% 2.11/0.67  fof(f285,plain,(
% 2.11/0.67    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl6_10),
% 2.11/0.67    inference(unit_resulting_resolution,[],[f43,f174,f56])).
% 2.11/0.67  fof(f56,plain,(
% 2.11/0.67    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f34])).
% 2.11/0.67  fof(f34,plain,(
% 2.11/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 2.11/0.67  fof(f33,plain,(
% 2.11/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f32,plain,(
% 2.11/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.67    inference(rectify,[],[f31])).
% 2.11/0.67  fof(f31,plain,(
% 2.11/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.67    inference(nnf_transformation,[],[f24])).
% 2.11/0.67  fof(f24,plain,(
% 2.11/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.11/0.67    inference(ennf_transformation,[],[f3])).
% 2.11/0.67  fof(f3,axiom,(
% 2.11/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.11/0.67  fof(f43,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f8])).
% 2.11/0.67  fof(f8,axiom,(
% 2.11/0.67    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.11/0.67  fof(f197,plain,(
% 2.11/0.67    ~spl6_11 | spl6_12 | ~spl6_10),
% 2.11/0.67    inference(avatar_split_clause,[],[f192,f172,f194,f176])).
% 2.11/0.67  fof(f192,plain,(
% 2.11/0.67    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl6_10),
% 2.11/0.67    inference(subsumption_resolution,[],[f191,f174])).
% 2.11/0.67  fof(f191,plain,(
% 2.11/0.67    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.11/0.67    inference(equality_resolution,[],[f79])).
% 2.11/0.67  fof(f79,plain,(
% 2.11/0.67    ( ! [X2] : (k3_xboole_0(sK0,sK1) != X2 | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),sK0) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),X2)) )),
% 2.11/0.67    inference(superposition,[],[f41,f67])).
% 2.11/0.67  fof(f67,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f40])).
% 2.11/0.67  fof(f179,plain,(
% 2.11/0.67    spl6_10 | spl6_11),
% 2.11/0.67    inference(avatar_split_clause,[],[f170,f176,f172])).
% 2.11/0.67  fof(f170,plain,(
% 2.11/0.67    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.11/0.67    inference(equality_resolution,[],[f77])).
% 2.11/0.67  fof(f77,plain,(
% 2.11/0.67    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 2.11/0.67    inference(superposition,[],[f41,f65])).
% 2.11/0.67  fof(f65,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f40])).
% 2.11/0.67  % SZS output end Proof for theBenchmark
% 2.11/0.67  % (18467)------------------------------
% 2.11/0.67  % (18467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.67  % (18467)Termination reason: Refutation
% 2.11/0.67  
% 2.11/0.67  % (18467)Memory used [KB]: 11385
% 2.11/0.67  % (18467)Time elapsed: 0.253 s
% 2.11/0.67  % (18467)------------------------------
% 2.11/0.67  % (18467)------------------------------
% 2.11/0.69  % (18440)Success in time 0.328 s
%------------------------------------------------------------------------------
