%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0946+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 285 expanded)
%              Number of leaves         :   25 ( 100 expanded)
%              Depth                    :   15
%              Number of atoms          :  407 (1105 expanded)
%              Number of equality atoms :   58 ( 177 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f85,f92,f97,f111,f152,f159,f170,f177])).

fof(f177,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f175,f84])).

fof(f84,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_4
  <=> r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f175,plain,
    ( ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f172,f147])).

fof(f147,plain,
    ( sK3 = k1_wellord1(k1_wellord2(sK2),sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_8
  <=> sK3 = k1_wellord1(k1_wellord2(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f172,plain,
    ( ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(k1_wellord1(k1_wellord2(sK2),sK3)))
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f91,f169,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(k1_wellord1(k1_wellord2(X1),X0)))
      | ~ r2_hidden(X0,X1)
      | ~ v2_wellord1(k1_wellord2(X1)) ) ),
    inference(forward_demodulation,[],[f136,f122])).

fof(f122,plain,(
    ! [X0,X1] : k1_wellord2(k1_wellord1(k1_wellord2(X0),X1)) = k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)) ),
    inference(unit_resulting_resolution,[],[f103,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(k1_wellord1(k1_wellord2(X0),X1),X0) ),
    inference(backward_demodulation,[],[f99,f102])).

fof(f102,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f101,f98])).

fof(f98,plain,(
    ! [X0,X1] : sP1(X0,k1_wellord2(X1)) ),
    inference(unit_resulting_resolution,[],[f43,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f25,f28,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
            <=> r1_tarski(X2,X3) )
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        & k3_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f101,plain,(
    ! [X0] :
      ( ~ sP1(X0,k1_wellord2(X0))
      | k3_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(resolution,[],[f61,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k3_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
            | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
          & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
            | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
          & r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X1) )
        | k3_relat_1(X0) != X1 )
      & ( ( ! [X4,X5] :
              ( ( ( r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r1_tarski(X4,X5) )
                & ( r1_tarski(X4,X5)
                  | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          & k3_relat_1(X0) = X1 )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X0) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
        & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X0) )
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | k3_relat_1(X0) != X1 )
      & ( ( ! [X4,X5] :
              ( ( ( r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r1_tarski(X4,X5) )
                & ( r1_tarski(X4,X5)
                  | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          & k3_relat_1(X0) = X1 )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X1) )
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | k3_relat_1(X1) != X0 )
      & ( ( ! [X2,X3] :
              ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                  | ~ r1_tarski(X2,X3) )
                & ( r1_tarski(X2,X3)
                  | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X1) )
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | k3_relat_1(X1) != X0 )
      & ( ( ! [X2,X3] :
              ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                  | ~ r1_tarski(X2,X3) )
                & ( r1_tarski(X2,X3)
                  | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0] :
      ( sP0(k1_wellord2(X0),X0)
      | ~ sP1(X0,k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | k1_wellord2(X0) != X1
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

% (14552)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k1_wellord2(X0) != X1 ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(k1_wellord1(k1_wellord2(X0),X1),k3_relat_1(k1_wellord2(X0))) ),
    inference(unit_resulting_resolution,[],[f43,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v2_wellord1(k1_wellord2(X1))
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) ) ),
    inference(forward_demodulation,[],[f135,f102])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
      | ~ v2_wellord1(k1_wellord2(X1))
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) ) ),
    inference(resolution,[],[f44,f43])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(f169,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl6_10
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f91,plain,
    ( v2_wellord1(k1_wellord2(sK2))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_5
  <=> v2_wellord1(k1_wellord2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f170,plain,
    ( spl6_10
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_9 ),
    inference(avatar_split_clause,[],[f164,f149,f77,f72,f67,f167])).

fof(f67,plain,
    ( spl6_1
  <=> v3_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f72,plain,
    ( spl6_2
  <=> v3_ordinal1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f77,plain,
    ( spl6_3
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f149,plain,
    ( spl6_9
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f164,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f69,f74,f79,f150,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f150,plain,
    ( ~ r2_hidden(sK2,sK3)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f79,plain,
    ( sK2 != sK3
    | spl6_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f74,plain,
    ( v3_ordinal1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f69,plain,
    ( v3_ordinal1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f159,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f157,f110])).

fof(f110,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_7
  <=> r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f157,plain,
    ( ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f154,f155])).

fof(f155,plain,
    ( sK2 = k1_wellord1(k1_wellord2(sK3),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f69,f74,f151,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

fof(f151,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f154,plain,
    ( ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(k1_wellord1(k1_wellord2(sK3),sK2)))
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f96,f151,f137])).

% (14552)Refutation not found, incomplete strategy% (14552)------------------------------
% (14552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14552)Termination reason: Refutation not found, incomplete strategy

% (14552)Memory used [KB]: 10490
% (14552)Time elapsed: 0.082 s
% (14552)------------------------------
% (14552)------------------------------
fof(f96,plain,
    ( v2_wellord1(k1_wellord2(sK3))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f94])).

% (14560)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f94,plain,
    ( spl6_6
  <=> v2_wellord1(k1_wellord2(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f152,plain,
    ( spl6_8
    | spl6_9
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f143,f77,f72,f67,f149,f145])).

fof(f143,plain,
    ( r2_hidden(sK2,sK3)
    | sK3 = k1_wellord1(k1_wellord2(sK2),sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f142,f79])).

fof(f142,plain,
    ( r2_hidden(sK2,sK3)
    | sK2 = sK3
    | sK3 = k1_wellord1(k1_wellord2(sK2),sK3)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f131,f74])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(sK2,X0)
        | sK2 = X0
        | k1_wellord1(k1_wellord2(sK2),X0) = X0 )
    | ~ spl6_1 ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,X0)
        | ~ v3_ordinal1(X0)
        | sK2 = X0
        | k1_wellord1(k1_wellord2(sK2),X0) = X0
        | ~ v3_ordinal1(X0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f127,f125])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | k1_wellord1(k1_wellord2(sK2),X0) = X0
        | ~ v3_ordinal1(X0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f47,f69])).

fof(f127,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | r2_hidden(sK2,X0)
        | ~ v3_ordinal1(X0)
        | sK2 = X0 )
    | ~ spl6_1 ),
    inference(resolution,[],[f48,f69])).

fof(f111,plain,
    ( spl6_7
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f104,f82,f108])).

fof(f104,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f43,f43,f84,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(f97,plain,
    ( spl6_6
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f87,f72,f94])).

% (14571)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f87,plain,
    ( v2_wellord1(k1_wellord2(sK3))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f74,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(f92,plain,
    ( spl6_5
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f86,f67,f89])).

fof(f86,plain,
    ( v2_wellord1(k1_wellord2(sK2))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f69,f46])).

fof(f85,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f41,f82])).

fof(f41,plain,(
    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK2 != sK3
    & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f13,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK2 != X1
          & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( sK2 != X1
        & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK2 != sK3
      & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
      & v3_ordinal1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

fof(f80,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f42,f77])).

% (14554)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f42,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f40,f72])).

fof(f40,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f39,f67])).

fof(f39,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f32])).

%------------------------------------------------------------------------------
