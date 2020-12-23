%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0476+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 114 expanded)
%              Number of leaves         :   14 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  188 ( 305 expanded)
%              Number of equality atoms :   38 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1017,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f62,f85,f109,f339,f360,f380,f403,f962,f998,f1016])).

fof(f1016,plain,
    ( ~ spl9_2
    | spl9_3
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(avatar_contradiction_clause,[],[f1014])).

fof(f1014,plain,
    ( $false
    | ~ spl9_2
    | spl9_3
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f58,f999])).

fof(f999,plain,
    ( r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0)
    | ~ spl9_2
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(backward_demodulation,[],[f963,f997])).

fof(f997,plain,
    ( sK6(k6_relat_1(sK0),sK0) = sK8(k6_relat_1(sK0),sK0)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f995])).

fof(f995,plain,
    ( spl9_18
  <=> sK6(k6_relat_1(sK0),sK0) = sK8(k6_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f963,plain,
    ( r2_hidden(sK8(k6_relat_1(sK0),sK0),sK0)
    | ~ spl9_2
    | ~ spl9_17 ),
    inference(resolution,[],[f961,f410])).

fof(f410,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(sK0))
        | r2_hidden(X0,sK0) )
    | ~ spl9_2 ),
    inference(superposition,[],[f30,f39])).

fof(f39,plain,
    ( sK0 = k1_relat_1(k6_relat_1(sK0))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl9_2
  <=> sK0 = k1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f30,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f961,plain,
    ( r2_hidden(k4_tarski(sK8(k6_relat_1(sK0),sK0),sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f959])).

fof(f959,plain,
    ( spl9_17
  <=> r2_hidden(k4_tarski(sK8(k6_relat_1(sK0),sK0),sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f58,plain,
    ( ~ r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl9_3
  <=> r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f998,plain,
    ( spl9_18
    | ~ spl9_6
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f965,f959,f73,f995])).

fof(f73,plain,
    ( spl9_6
  <=> v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f965,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | sK6(k6_relat_1(sK0),sK0) = sK8(k6_relat_1(sK0),sK0)
    | ~ spl9_17 ),
    inference(resolution,[],[f961,f27])).

fof(f27,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | X2 = X3
      | ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | X2 = X3
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(f962,plain,
    ( spl9_1
    | spl9_17
    | spl9_3 ),
    inference(avatar_split_clause,[],[f112,f56,f959,f34])).

fof(f34,plain,
    ( spl9_1
  <=> sK0 = k2_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f112,plain,
    ( r2_hidden(k4_tarski(sK8(k6_relat_1(sK0),sK0),sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0))
    | sK0 = k2_relat_1(k6_relat_1(sK0))
    | spl9_3 ),
    inference(resolution,[],[f58,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f403,plain,
    ( ~ spl9_10
    | ~ spl9_6
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f362,f337,f73,f333])).

fof(f333,plain,
    ( spl9_10
  <=> r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f337,plain,
    ( spl9_11
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f362,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0)
    | ~ spl9_11 ),
    inference(resolution,[],[f338,f26])).

fof(f26,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | X2 != X3
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f338,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f337])).

fof(f380,plain,
    ( spl9_2
    | spl9_10
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f365,f337,f333,f38])).

fof(f365,plain,
    ( r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0)
    | sK0 = k1_relat_1(k6_relat_1(sK0))
    | ~ spl9_11 ),
    inference(resolution,[],[f338,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f360,plain,
    ( spl9_11
    | ~ spl9_6
    | spl9_10 ),
    inference(avatar_split_clause,[],[f341,f333,f73,f337])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k6_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0)) )
    | spl9_10 ),
    inference(resolution,[],[f335,f28])).

fof(f28,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | r2_hidden(X2,X0)
      | ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f335,plain,
    ( ~ r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0)
    | spl9_10 ),
    inference(avatar_component_clause,[],[f333])).

fof(f339,plain,
    ( ~ spl9_10
    | spl9_11
    | spl9_2 ),
    inference(avatar_split_clause,[],[f77,f38,f337,f333])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0))
        | ~ r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0) )
    | spl9_2 ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,
    ( ! [X2,X1] :
        ( sK0 != X1
        | ~ r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),X1),X2),k6_relat_1(sK0))
        | ~ r2_hidden(sK3(k6_relat_1(sK0),X1),X1) )
    | spl9_2 ),
    inference(superposition,[],[f40,f20])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,
    ( sK0 != k1_relat_1(k6_relat_1(sK0))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f109,plain,
    ( ~ spl9_3
    | ~ spl9_6
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f93,f60,f73,f56])).

fof(f60,plain,
    ( spl9_4
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f93,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f61,f26])).

fof(f61,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f85,plain,(
    spl9_6 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl9_6 ),
    inference(resolution,[],[f75,f10])).

fof(f10,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f75,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl9_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f62,plain,
    ( ~ spl9_3
    | spl9_4
    | spl9_1 ),
    inference(avatar_split_clause,[],[f54,f34,f60,f56])).

fof(f54,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0))
        | ~ r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0) )
    | spl9_1 ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,
    ( ! [X2,X1] :
        ( sK0 != X1
        | ~ r2_hidden(k4_tarski(X2,sK6(k6_relat_1(sK0),X1)),k6_relat_1(sK0))
        | ~ r2_hidden(sK6(k6_relat_1(sK0),X1),X1) )
    | spl9_1 ),
    inference(superposition,[],[f36,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,
    ( sK0 != k2_relat_1(k6_relat_1(sK0))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f41,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f9,f38,f34])).

fof(f9,plain,
    ( sK0 != k1_relat_1(k6_relat_1(sK0))
    | sK0 != k2_relat_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( k2_relat_1(k6_relat_1(X0)) != X0
      | k1_relat_1(k6_relat_1(X0)) != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( k2_relat_1(k6_relat_1(X0)) = X0
        & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

%------------------------------------------------------------------------------
