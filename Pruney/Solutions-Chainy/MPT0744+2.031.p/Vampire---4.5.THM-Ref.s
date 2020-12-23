%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 217 expanded)
%              Number of leaves         :   13 (  55 expanded)
%              Depth                    :   27
%              Number of atoms          :  378 (1172 expanded)
%              Number of equality atoms :   64 ( 115 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f304,plain,(
    $false ),
    inference(subsumption_resolution,[],[f302,f59])).

fof(f59,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r1_ordinal1(sK1,sK2)
      | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
    & ( r1_ordinal1(sK1,sK2)
      | r2_hidden(sK1,k1_ordinal1(sK2)) )
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK1,X1)
            | ~ r2_hidden(sK1,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK1,X1)
            | r2_hidden(sK1,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK1,X1)
          | ~ r2_hidden(sK1,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK1,X1)
          | r2_hidden(sK1,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK1,sK2)
        | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
      & ( r1_ordinal1(sK1,sK2)
        | r2_hidden(sK1,k1_ordinal1(sK2)) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f302,plain,(
    ~ v3_ordinal1(sK2) ),
    inference(resolution,[],[f295,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f295,plain,(
    ~ v1_ordinal1(sK2) ),
    inference(subsumption_resolution,[],[f294,f58])).

fof(f58,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f294,plain,
    ( ~ v1_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f292,f110])).

fof(f110,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f292,plain,
    ( ~ v1_ordinal1(sK2)
    | ~ r1_tarski(sK1,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,
    ( ~ v1_ordinal1(sK2)
    | ~ r1_tarski(sK1,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f267,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f267,plain,
    ( ~ r1_ordinal1(sK1,sK1)
    | ~ v1_ordinal1(sK2) ),
    inference(subsumption_resolution,[],[f261,f113])).

fof(f113,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

% (19357)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f261,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ r1_ordinal1(sK1,sK1)
    | ~ v1_ordinal1(sK2) ),
    inference(superposition,[],[f169,f241])).

fof(f241,plain,
    ( sK1 = sK2
    | ~ v1_ordinal1(sK2) ),
    inference(resolution,[],[f240,f159])).

fof(f159,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ v1_ordinal1(sK2) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ v1_ordinal1(sK2) ),
    inference(resolution,[],[f157,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f157,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f156,f58])).

fof(f156,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ v3_ordinal1(sK1)
    | ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f153,f59])).

fof(f153,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f71,f134])).

fof(f134,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f132,f61])).

fof(f61,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK2))
    | ~ r1_ordinal1(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f132,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_ordinal1(X0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f116,f63])).

fof(f63,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f116,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f50,plain,(
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

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

% (19347)Termination reason: Refutation not found, incomplete strategy
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f240,plain,
    ( r2_hidden(sK1,sK2)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f239,f59])).

fof(f239,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,sK2)
    | ~ v3_ordinal1(sK2) ),
    inference(subsumption_resolution,[],[f238,f58])).

fof(f238,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,sK2)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK2) ),
    inference(duplicate_literal_removal,[],[f236])).

fof(f236,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,sK2)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK2)
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f225,f148])).

fof(f148,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r2_hidden(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r2_hidden(X3,X2)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f70,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f225,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK1 = sK2
    | r2_hidden(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,
    ( r2_hidden(sK1,sK2)
    | sK1 = sK2
    | sK1 = sK2
    | ~ r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f214,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f214,plain,
    ( r1_tarski(sK1,sK2)
    | r2_hidden(sK1,sK2)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f213,f58])).

fof(f213,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,sK2)
    | r1_tarski(sK1,sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f212,f59])).

fof(f212,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,sK2)
    | r1_tarski(sK1,sK2)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f209,f70])).

fof(f209,plain,
    ( r1_ordinal1(sK1,sK2)
    | sK1 = sK2
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f205,f60])).

fof(f60,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK2))
    | r1_ordinal1(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(resolution,[],[f162,f114])).

fof(f114,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f162,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_tarski(X0))
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_ordinal1(X0)) ) ),
    inference(superposition,[],[f117,f63])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f169,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK2))
    | ~ r1_ordinal1(sK1,sK2) ),
    inference(resolution,[],[f130,f61])).

fof(f130,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_ordinal1(X0))
      | ~ r2_hidden(X1,k1_tarski(X0)) ) ),
    inference(superposition,[],[f115,f63])).

fof(f115,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:34:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (19334)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (19338)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (19356)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (19348)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (19340)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (19338)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 1.36/0.54  % (19333)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.36/0.54  % (19345)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.36/0.54  % (19353)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.36/0.54  % (19355)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.36/0.54  % (19350)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.36/0.54  % (19358)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.36/0.54  % (19347)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.36/0.54  % (19332)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.36/0.55  % (19347)Refutation not found, incomplete strategy% (19347)------------------------------
% 1.36/0.55  % (19347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (19342)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.36/0.55  % (19358)Refutation not found, incomplete strategy% (19358)------------------------------
% 1.36/0.55  % (19358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (19358)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (19358)Memory used [KB]: 1663
% 1.36/0.55  % (19358)Time elapsed: 0.089 s
% 1.36/0.55  % (19358)------------------------------
% 1.36/0.55  % (19358)------------------------------
% 1.36/0.55  % (19337)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.36/0.55  % (19345)Refutation not found, incomplete strategy% (19345)------------------------------
% 1.36/0.55  % (19345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (19329)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.36/0.55  % (19345)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (19345)Memory used [KB]: 10746
% 1.36/0.55  % (19345)Time elapsed: 0.128 s
% 1.36/0.55  % (19345)------------------------------
% 1.36/0.55  % (19345)------------------------------
% 1.36/0.55  % (19354)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.36/0.55  % SZS output start Proof for theBenchmark
% 1.36/0.55  fof(f304,plain,(
% 1.36/0.55    $false),
% 1.36/0.55    inference(subsumption_resolution,[],[f302,f59])).
% 1.36/0.55  fof(f59,plain,(
% 1.36/0.55    v3_ordinal1(sK2)),
% 1.36/0.55    inference(cnf_transformation,[],[f39])).
% 1.36/0.55  fof(f39,plain,(
% 1.36/0.55    ((~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))) & v3_ordinal1(sK2)) & v3_ordinal1(sK1)),
% 1.36/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).
% 1.36/0.55  fof(f37,plain,(
% 1.36/0.55    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK1,X1) | ~r2_hidden(sK1,k1_ordinal1(X1))) & (r1_ordinal1(sK1,X1) | r2_hidden(sK1,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK1))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f38,plain,(
% 1.36/0.55    ? [X1] : ((~r1_ordinal1(sK1,X1) | ~r2_hidden(sK1,k1_ordinal1(X1))) & (r1_ordinal1(sK1,X1) | r2_hidden(sK1,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))) & v3_ordinal1(sK2))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f36,plain,(
% 1.36/0.55    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.36/0.55    inference(flattening,[],[f35])).
% 1.36/0.55  fof(f35,plain,(
% 1.36/0.55    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.36/0.55    inference(nnf_transformation,[],[f23])).
% 1.36/0.55  fof(f23,plain,(
% 1.36/0.55    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f20])).
% 1.36/0.55  fof(f20,negated_conjecture,(
% 1.36/0.55    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.36/0.55    inference(negated_conjecture,[],[f19])).
% 1.36/0.55  fof(f19,conjecture,(
% 1.36/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.36/0.55  fof(f302,plain,(
% 1.36/0.55    ~v3_ordinal1(sK2)),
% 1.36/0.55    inference(resolution,[],[f295,f64])).
% 1.36/0.55  fof(f64,plain,(
% 1.36/0.55    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f24])).
% 1.36/0.55  fof(f24,plain,(
% 1.36/0.55    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f22])).
% 1.36/0.55  fof(f22,plain,(
% 1.36/0.55    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 1.36/0.55    inference(pure_predicate_removal,[],[f13])).
% 1.36/0.55  fof(f13,axiom,(
% 1.36/0.55    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 1.36/0.55  fof(f295,plain,(
% 1.36/0.55    ~v1_ordinal1(sK2)),
% 1.36/0.55    inference(subsumption_resolution,[],[f294,f58])).
% 1.36/0.55  fof(f58,plain,(
% 1.36/0.55    v3_ordinal1(sK1)),
% 1.36/0.55    inference(cnf_transformation,[],[f39])).
% 1.36/0.55  fof(f294,plain,(
% 1.36/0.55    ~v1_ordinal1(sK2) | ~v3_ordinal1(sK1)),
% 1.36/0.55    inference(subsumption_resolution,[],[f292,f110])).
% 1.36/0.55  fof(f110,plain,(
% 1.36/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.36/0.55    inference(equality_resolution,[],[f73])).
% 1.36/0.55  fof(f73,plain,(
% 1.36/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.36/0.55    inference(cnf_transformation,[],[f42])).
% 1.36/0.55  fof(f42,plain,(
% 1.36/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.55    inference(flattening,[],[f41])).
% 1.36/0.55  fof(f41,plain,(
% 1.36/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.55    inference(nnf_transformation,[],[f2])).
% 1.36/0.55  fof(f2,axiom,(
% 1.36/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.55  fof(f292,plain,(
% 1.36/0.55    ~v1_ordinal1(sK2) | ~r1_tarski(sK1,sK1) | ~v3_ordinal1(sK1)),
% 1.36/0.55    inference(duplicate_literal_removal,[],[f286])).
% 1.50/0.55  fof(f286,plain,(
% 1.50/0.55    ~v1_ordinal1(sK2) | ~r1_tarski(sK1,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK1)),
% 1.50/0.55    inference(resolution,[],[f267,f71])).
% 1.50/0.55  fof(f71,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f40])).
% 1.50/0.55  fof(f40,plain,(
% 1.50/0.55    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.50/0.55    inference(nnf_transformation,[],[f31])).
% 1.50/0.55  fof(f31,plain,(
% 1.50/0.55    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.50/0.55    inference(flattening,[],[f30])).
% 1.50/0.55  fof(f30,plain,(
% 1.50/0.55    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.50/0.55    inference(ennf_transformation,[],[f17])).
% 1.50/0.55  fof(f17,axiom,(
% 1.50/0.55    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.50/0.55  fof(f267,plain,(
% 1.50/0.55    ~r1_ordinal1(sK1,sK1) | ~v1_ordinal1(sK2)),
% 1.50/0.55    inference(subsumption_resolution,[],[f261,f113])).
% 1.50/0.55  fof(f113,plain,(
% 1.50/0.55    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.50/0.55    inference(equality_resolution,[],[f112])).
% 1.50/0.55  fof(f112,plain,(
% 1.50/0.55    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.50/0.55    inference(equality_resolution,[],[f76])).
% 1.50/0.55  fof(f76,plain,(
% 1.50/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.50/0.55    inference(cnf_transformation,[],[f46])).
% 1.50/0.55  fof(f46,plain,(
% 1.50/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.50/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 1.50/0.55  fof(f45,plain,(
% 1.50/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.50/0.55    introduced(choice_axiom,[])).
% 1.50/0.55  fof(f44,plain,(
% 1.50/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.50/0.55    inference(rectify,[],[f43])).
% 1.50/0.55  fof(f43,plain,(
% 1.50/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.50/0.55    inference(nnf_transformation,[],[f3])).
% 1.50/0.55  % (19357)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.50/0.55  fof(f3,axiom,(
% 1.50/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.50/0.55  fof(f261,plain,(
% 1.50/0.55    ~r2_hidden(sK1,k1_tarski(sK1)) | ~r1_ordinal1(sK1,sK1) | ~v1_ordinal1(sK2)),
% 1.50/0.55    inference(superposition,[],[f169,f241])).
% 1.50/0.55  fof(f241,plain,(
% 1.50/0.55    sK1 = sK2 | ~v1_ordinal1(sK2)),
% 1.50/0.55    inference(resolution,[],[f240,f159])).
% 1.50/0.55  fof(f159,plain,(
% 1.50/0.55    ~r2_hidden(sK1,sK2) | ~v1_ordinal1(sK2)),
% 1.50/0.55    inference(duplicate_literal_removal,[],[f158])).
% 1.50/0.55  fof(f158,plain,(
% 1.50/0.55    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,sK2) | ~v1_ordinal1(sK2)),
% 1.50/0.55    inference(resolution,[],[f157,f66])).
% 1.50/0.55  fof(f66,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f27])).
% 1.50/0.55  fof(f27,plain,(
% 1.50/0.55    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 1.50/0.55    inference(ennf_transformation,[],[f21])).
% 1.50/0.55  fof(f21,plain,(
% 1.50/0.55    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 1.50/0.55    inference(unused_predicate_definition_removal,[],[f16])).
% 1.50/0.55  fof(f16,axiom,(
% 1.50/0.55    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 1.50/0.55  fof(f157,plain,(
% 1.50/0.55    ~r1_tarski(sK1,sK2) | ~r2_hidden(sK1,sK2)),
% 1.50/0.55    inference(subsumption_resolution,[],[f156,f58])).
% 1.50/0.55  fof(f156,plain,(
% 1.50/0.55    ~r1_tarski(sK1,sK2) | ~v3_ordinal1(sK1) | ~r2_hidden(sK1,sK2)),
% 1.50/0.55    inference(subsumption_resolution,[],[f153,f59])).
% 1.50/0.55  fof(f153,plain,(
% 1.50/0.55    ~r1_tarski(sK1,sK2) | ~v3_ordinal1(sK2) | ~v3_ordinal1(sK1) | ~r2_hidden(sK1,sK2)),
% 1.50/0.55    inference(resolution,[],[f71,f134])).
% 1.50/0.55  fof(f134,plain,(
% 1.50/0.55    ~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,sK2)),
% 1.50/0.55    inference(resolution,[],[f132,f61])).
% 1.50/0.55  fof(f61,plain,(
% 1.50/0.55    ~r2_hidden(sK1,k1_ordinal1(sK2)) | ~r1_ordinal1(sK1,sK2)),
% 1.50/0.55    inference(cnf_transformation,[],[f39])).
% 1.50/0.55  fof(f132,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r2_hidden(X1,k1_ordinal1(X0)) | ~r2_hidden(X1,X0)) )),
% 1.50/0.55    inference(superposition,[],[f116,f63])).
% 1.50/0.55  fof(f63,plain,(
% 1.50/0.55    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f15])).
% 1.50/0.55  fof(f15,axiom,(
% 1.50/0.55    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.50/0.55  fof(f116,plain,(
% 1.50/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 1.50/0.55    inference(equality_resolution,[],[f81])).
% 1.50/0.55  fof(f81,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.50/0.55    inference(cnf_transformation,[],[f51])).
% 1.50/0.55  fof(f51,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).
% 1.50/0.55  fof(f50,plain,(
% 1.50/0.55    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.50/0.55    introduced(choice_axiom,[])).
% 1.50/0.55  fof(f49,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/0.55    inference(rectify,[],[f48])).
% 1.50/0.55  fof(f48,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/0.55    inference(flattening,[],[f47])).
% 1.50/0.55  fof(f47,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/0.55    inference(nnf_transformation,[],[f1])).
% 1.50/0.55  % (19347)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  fof(f1,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.50/0.55  fof(f240,plain,(
% 1.50/0.55    r2_hidden(sK1,sK2) | sK1 = sK2),
% 1.50/0.55    inference(subsumption_resolution,[],[f239,f59])).
% 1.50/0.55  fof(f239,plain,(
% 1.50/0.55    sK1 = sK2 | r2_hidden(sK1,sK2) | ~v3_ordinal1(sK2)),
% 1.50/0.55    inference(subsumption_resolution,[],[f238,f58])).
% 1.50/0.55  fof(f238,plain,(
% 1.50/0.55    sK1 = sK2 | r2_hidden(sK1,sK2) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK2)),
% 1.50/0.55    inference(duplicate_literal_removal,[],[f236])).
% 1.50/0.55  fof(f236,plain,(
% 1.50/0.55    sK1 = sK2 | r2_hidden(sK1,sK2) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK2) | r2_hidden(sK1,sK2)),
% 1.50/0.55    inference(resolution,[],[f225,f148])).
% 1.50/0.55  fof(f148,plain,(
% 1.50/0.55    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r2_hidden(X3,X2)) )),
% 1.50/0.55    inference(duplicate_literal_removal,[],[f146])).
% 1.50/0.55  fof(f146,plain,(
% 1.50/0.55    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r2_hidden(X3,X2) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2)) )),
% 1.50/0.55    inference(resolution,[],[f70,f65])).
% 1.50/0.55  fof(f65,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f26])).
% 1.50/0.55  fof(f26,plain,(
% 1.50/0.55    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.50/0.55    inference(flattening,[],[f25])).
% 1.50/0.55  fof(f25,plain,(
% 1.50/0.55    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.50/0.55    inference(ennf_transformation,[],[f18])).
% 1.50/0.55  fof(f18,axiom,(
% 1.50/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.50/0.55  fof(f70,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f40])).
% 1.50/0.55  fof(f225,plain,(
% 1.50/0.55    ~r1_tarski(sK2,sK1) | sK1 = sK2 | r2_hidden(sK1,sK2)),
% 1.50/0.55    inference(duplicate_literal_removal,[],[f224])).
% 1.50/0.55  fof(f224,plain,(
% 1.50/0.55    r2_hidden(sK1,sK2) | sK1 = sK2 | sK1 = sK2 | ~r1_tarski(sK2,sK1)),
% 1.50/0.55    inference(resolution,[],[f214,f74])).
% 1.50/0.55  fof(f74,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f42])).
% 1.50/0.55  fof(f214,plain,(
% 1.50/0.55    r1_tarski(sK1,sK2) | r2_hidden(sK1,sK2) | sK1 = sK2),
% 1.50/0.55    inference(subsumption_resolution,[],[f213,f58])).
% 1.50/0.55  fof(f213,plain,(
% 1.50/0.55    sK1 = sK2 | r2_hidden(sK1,sK2) | r1_tarski(sK1,sK2) | ~v3_ordinal1(sK1)),
% 1.50/0.55    inference(subsumption_resolution,[],[f212,f59])).
% 1.50/0.55  fof(f212,plain,(
% 1.50/0.55    sK1 = sK2 | r2_hidden(sK1,sK2) | r1_tarski(sK1,sK2) | ~v3_ordinal1(sK2) | ~v3_ordinal1(sK1)),
% 1.50/0.55    inference(resolution,[],[f209,f70])).
% 1.50/0.55  fof(f209,plain,(
% 1.50/0.55    r1_ordinal1(sK1,sK2) | sK1 = sK2 | r2_hidden(sK1,sK2)),
% 1.50/0.55    inference(resolution,[],[f205,f60])).
% 1.50/0.55  fof(f60,plain,(
% 1.50/0.55    r2_hidden(sK1,k1_ordinal1(sK2)) | r1_ordinal1(sK1,sK2)),
% 1.50/0.55    inference(cnf_transformation,[],[f39])).
% 1.50/0.55  fof(f205,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | r2_hidden(X0,X1) | X0 = X1) )),
% 1.50/0.55    inference(resolution,[],[f162,f114])).
% 1.50/0.55  fof(f114,plain,(
% 1.50/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.50/0.55    inference(equality_resolution,[],[f75])).
% 1.50/0.55  fof(f75,plain,(
% 1.50/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.50/0.55    inference(cnf_transformation,[],[f46])).
% 1.50/0.55  fof(f162,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r2_hidden(X1,k1_tarski(X0)) | r2_hidden(X1,X0) | ~r2_hidden(X1,k1_ordinal1(X0))) )),
% 1.50/0.55    inference(superposition,[],[f117,f63])).
% 1.50/0.55  fof(f117,plain,(
% 1.50/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 1.50/0.55    inference(equality_resolution,[],[f80])).
% 1.50/0.55  fof(f80,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.50/0.55    inference(cnf_transformation,[],[f51])).
% 1.50/0.55  fof(f169,plain,(
% 1.50/0.55    ~r2_hidden(sK1,k1_tarski(sK2)) | ~r1_ordinal1(sK1,sK2)),
% 1.50/0.55    inference(resolution,[],[f130,f61])).
% 1.50/0.55  fof(f130,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r2_hidden(X1,k1_ordinal1(X0)) | ~r2_hidden(X1,k1_tarski(X0))) )),
% 1.50/0.55    inference(superposition,[],[f115,f63])).
% 1.50/0.55  fof(f115,plain,(
% 1.50/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.50/0.55    inference(equality_resolution,[],[f82])).
% 1.50/0.55  fof(f82,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.50/0.55    inference(cnf_transformation,[],[f51])).
% 1.50/0.55  % SZS output end Proof for theBenchmark
% 1.50/0.55  % (19338)------------------------------
% 1.50/0.55  % (19338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (19338)Termination reason: Refutation
% 1.50/0.55  
% 1.50/0.55  % (19338)Memory used [KB]: 1918
% 1.50/0.55  % (19338)Time elapsed: 0.115 s
% 1.50/0.55  % (19338)------------------------------
% 1.50/0.55  % (19338)------------------------------
% 1.50/0.55  
% 1.50/0.55  % (19347)Memory used [KB]: 1791
% 1.50/0.55  % (19347)Time elapsed: 0.126 s
% 1.50/0.55  % (19347)------------------------------
% 1.50/0.55  % (19347)------------------------------
% 1.50/0.55  % (19331)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.50/0.56  % (19328)Success in time 0.196 s
%------------------------------------------------------------------------------
