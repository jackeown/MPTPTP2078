%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0610+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  74 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :   16
%              Number of atoms          :  132 ( 242 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f46,f53,f135])).

fof(f135,plain,
    ( ~ spl9_1
    | spl9_3
    | ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl9_1
    | spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f133,f45])).

fof(f45,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl9_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f133,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( r1_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1)
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f124,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f124,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(X1,sK1),sK0)
        | r1_xboole_0(X1,sK1) )
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f119,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f115,f69])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( sP7(sK3(X0),X1)
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_1 ),
    inference(superposition,[],[f25,f47])).

fof(f47,plain,
    ( ! [X0] :
        ( k4_tarski(sK3(X0),sK4(X0)) = X0
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_1 ),
    inference(resolution,[],[f35,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_tarski(sK3(X1),sK4(X1)) = X1
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f35,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl9_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f25,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | sP7(X2,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f115,plain,
    ( ! [X0] :
        ( ~ sP7(sK3(X0),sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f95,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_relat_1(X0))
      | ~ sP7(X2,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0),k1_relat_1(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK3(X0),k1_relat_1(sK0)) )
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f69,f63])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ sP7(X0,sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl9_4 ),
    inference(resolution,[],[f55,f31])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl9_4 ),
    inference(resolution,[],[f52,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,
    ( r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl9_4
  <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f53,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f14,f50])).

fof(f14,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

fof(f46,plain,(
    ~ spl9_3 ),
    inference(avatar_split_clause,[],[f15,f43])).

fof(f15,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f13,f33])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
