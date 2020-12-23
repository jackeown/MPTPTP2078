%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0004+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 105 expanded)
%              Number of leaves         :   12 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  134 ( 282 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f170,f175,f176,f205,f217,f240])).

fof(f240,plain,
    ( ~ spl15_1
    | spl15_2 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl15_1
    | spl15_2 ),
    inference(trivial_inequality_removal,[],[f236])).

fof(f236,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | ~ spl15_1
    | spl15_2 ),
    inference(superposition,[],[f206,f216])).

fof(f216,plain,
    ( o_0_0_xboole_0 = k3_xboole_0(sK3,sK4)
    | ~ spl15_1 ),
    inference(resolution,[],[f214,f148])).

fof(f148,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f95,f94])).

fof(f94,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f95,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f214,plain,
    ( v1_xboole_0(k3_xboole_0(sK3,sK4))
    | ~ spl15_1 ),
    inference(resolution,[],[f165,f97])).

fof(f97,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f53,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f165,plain,
    ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK3,sK4))
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl15_1
  <=> ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f206,plain,
    ( o_0_0_xboole_0 != k3_xboole_0(sK3,sK4)
    | spl15_2 ),
    inference(resolution,[],[f168,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != o_0_0_xboole_0 ) ),
    inference(definition_unfolding,[],[f112,f94])).

% (32137)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f112,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f168,plain,
    ( ~ r1_xboole_0(sK3,sK4)
    | spl15_2 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl15_2
  <=> r1_xboole_0(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f217,plain,
    ( ~ spl15_1
    | ~ spl15_3 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_3 ),
    inference(resolution,[],[f214,f177])).

fof(f177,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK3,sK4))
    | ~ spl15_3 ),
    inference(resolution,[],[f96,f174])).

fof(f174,plain,
    ( r2_hidden(sK5,k3_xboole_0(sK3,sK4))
    | ~ spl15_3 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl15_3
  <=> r2_hidden(sK5,k3_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f96,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f205,plain,
    ( ~ spl15_2
    | ~ spl15_3 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl15_2
    | ~ spl15_3 ),
    inference(resolution,[],[f202,f92])).

fof(f92,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f202,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl15_2
    | ~ spl15_3 ),
    inference(backward_demodulation,[],[f177,f196])).

fof(f196,plain,
    ( o_0_0_xboole_0 = k3_xboole_0(sK3,sK4)
    | ~ spl15_2 ),
    inference(resolution,[],[f151,f169])).

fof(f169,plain,
    ( r1_xboole_0(sK3,sK4)
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f167])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = o_0_0_xboole_0 ) ),
    inference(definition_unfolding,[],[f111,f94])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f176,plain,
    ( ~ spl15_2
    | spl15_3 ),
    inference(avatar_split_clause,[],[f88,f172,f167])).

fof(f88,plain,
    ( r2_hidden(sK5,k3_xboole_0(sK3,sK4))
    | ~ r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( r1_xboole_0(sK3,sK4)
      & r2_hidden(sK5,k3_xboole_0(sK3,sK4)) )
    | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK3,sK4))
      & ~ r1_xboole_0(sK3,sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f35,f50,f49])).

fof(f49,plain,
    ( ? [X0,X1] :
        ( ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) )
   => ( ( r1_xboole_0(sK3,sK4)
        & ? [X2] : r2_hidden(X2,k3_xboole_0(sK3,sK4)) )
      | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK3,sK4))
        & ~ r1_xboole_0(sK3,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X2] : r2_hidden(X2,k3_xboole_0(sK3,sK4))
   => r2_hidden(sK5,k3_xboole_0(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f175,plain,
    ( spl15_1
    | spl15_3 ),
    inference(avatar_split_clause,[],[f89,f172,f164])).

fof(f89,plain,(
    ! [X3] :
      ( r2_hidden(sK5,k3_xboole_0(sK3,sK4))
      | ~ r2_hidden(X3,k3_xboole_0(sK3,sK4)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f170,plain,
    ( spl15_1
    | spl15_2 ),
    inference(avatar_split_clause,[],[f91,f167,f164])).

fof(f91,plain,(
    ! [X3] :
      ( r1_xboole_0(sK3,sK4)
      | ~ r2_hidden(X3,k3_xboole_0(sK3,sK4)) ) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
