%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_0__t6_xboole_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:19 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  47 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 108 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f47,f69,f103])).

fof(f103,plain,
    ( ~ spl4_0
    | spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f89,f28])).

fof(f28,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t6_xboole_0.p',d8_xboole_0)).

fof(f89,plain,
    ( r2_xboole_0(sK0,sK0)
    | ~ spl4_0
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f87,f34])).

fof(f34,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_0
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f87,plain,
    ( sK0 = sK1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f85,f46])).

fof(f46,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_3
  <=> ~ r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f85,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f68,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f68,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_4
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f69,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f60,f67])).

fof(f60,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f37,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t6_xboole_0.p',d3_tarski)).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f18,f15])).

fof(f15,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( ~ r2_hidden(X2,X0)
                & r2_hidden(X2,X1) )
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t6_xboole_0.p',t6_xboole_0)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,
    ( ~ spl4_3
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f36,f33,f45])).

fof(f36,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ spl4_0 ),
    inference(resolution,[],[f26,f34])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t6_xboole_0.p',antisymmetry_r2_xboole_0)).

fof(f35,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
