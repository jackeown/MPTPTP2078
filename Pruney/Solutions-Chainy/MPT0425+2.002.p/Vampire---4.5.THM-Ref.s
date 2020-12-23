%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:30 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   57 (  86 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  230 ( 359 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(subsumption_resolution,[],[f228,f34])).

fof(f34,plain,(
    ~ r1_tarski(sK3,k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(sK3,k3_tarski(sK1))
    & ! [X3] :
        ( r1_xboole_0(X3,sK3)
        | ~ r2_hidden(X3,sK2) )
    & r1_tarski(sK3,k3_tarski(k2_xboole_0(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X2,k3_tarski(X0))
        & ! [X3] :
            ( r1_xboole_0(X3,X2)
            | ~ r2_hidden(X3,X1) )
        & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
   => ( ~ r1_tarski(sK3,k3_tarski(sK1))
      & ! [X3] :
          ( r1_xboole_0(X3,sK3)
          | ~ r2_hidden(X3,sK2) )
      & r1_tarski(sK3,k3_tarski(k2_xboole_0(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,k3_tarski(X0))
      & ! [X3] :
          ( r1_xboole_0(X3,X2)
          | ~ r2_hidden(X3,X1) )
      & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,k3_tarski(X0))
      & ! [X3] :
          ( r1_xboole_0(X3,X2)
          | ~ r2_hidden(X3,X1) )
      & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( r2_hidden(X3,X1)
             => r1_xboole_0(X3,X2) )
          & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
       => r1_tarski(X2,k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_xboole_0(X3,X2) )
        & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
     => r1_tarski(X2,k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_setfam_1)).

fof(f228,plain,(
    r1_tarski(sK3,k3_tarski(sK1)) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,
    ( r1_tarski(sK3,k3_tarski(sK1))
    | r1_tarski(sK3,k3_tarski(sK1)) ),
    inference(resolution,[],[f223,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f223,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(X0,k3_tarski(sK1)),sK3)
      | r1_tarski(X0,k3_tarski(sK1)) ) ),
    inference(resolution,[],[f222,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f222,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_tarski(sK1))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f213,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,k3_tarski(sK2)) ) ),
    inference(resolution,[],[f65,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f65,plain,(
    r1_xboole_0(k3_tarski(sK2),sK3) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,
    ( r1_xboole_0(k3_tarski(sK2),sK3)
    | r1_xboole_0(k3_tarski(sK2),sK3) ),
    inference(resolution,[],[f56,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(X0,sK3),sK2)
      | r1_xboole_0(k3_tarski(X0),sK3) ) ),
    inference(resolution,[],[f40,f33])).

fof(f33,plain,(
    ! [X3] :
      ( r1_xboole_0(X3,sK3)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(sK5(X0,X1),X1)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f213,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_tarski(sK1))
      | r2_hidden(X0,k3_tarski(sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f137,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_tarski(k2_xboole_0(sK1,sK2)))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    r1_tarski(sK3,k3_tarski(k2_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f137,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k3_tarski(k2_xboole_0(X4,X5)))
      | r2_hidden(X3,k3_tarski(X4))
      | r2_hidden(X3,k3_tarski(X5)) ) ),
    inference(resolution,[],[f44,f77])).

fof(f77,plain,(
    ! [X0,X1] : sP0(k3_tarski(X1),k3_tarski(X0),k3_tarski(k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f52,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f50])).

% (14016)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

% (14031)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f14])).

fof(f14,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
              & ~ r2_hidden(sK7(X0,X1,X2),X1) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( r2_hidden(sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X1)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).

% (14005)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (14003)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
            & ~ r2_hidden(sK7(X0,X1,X2),X1) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( r2_hidden(sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X1)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:41:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (14024)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.19/0.52  % (14017)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.19/0.52  % (14009)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.19/0.52  % (14008)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.19/0.53  % (14023)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.33/0.53  % (14002)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.53  % (14013)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.33/0.54  % (14014)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.54  % (14004)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.54  % (14018)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.54  % (14009)Refutation found. Thanks to Tanya!
% 1.33/0.54  % SZS status Theorem for theBenchmark
% 1.33/0.54  % SZS output start Proof for theBenchmark
% 1.33/0.54  fof(f229,plain,(
% 1.33/0.54    $false),
% 1.33/0.54    inference(subsumption_resolution,[],[f228,f34])).
% 1.33/0.54  fof(f34,plain,(
% 1.33/0.54    ~r1_tarski(sK3,k3_tarski(sK1))),
% 1.33/0.54    inference(cnf_transformation,[],[f17])).
% 1.33/0.54  fof(f17,plain,(
% 1.33/0.54    ~r1_tarski(sK3,k3_tarski(sK1)) & ! [X3] : (r1_xboole_0(X3,sK3) | ~r2_hidden(X3,sK2)) & r1_tarski(sK3,k3_tarski(k2_xboole_0(sK1,sK2)))),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f10,f16])).
% 1.33/0.54  fof(f16,plain,(
% 1.33/0.54    ? [X0,X1,X2] : (~r1_tarski(X2,k3_tarski(X0)) & ! [X3] : (r1_xboole_0(X3,X2) | ~r2_hidden(X3,X1)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))) => (~r1_tarski(sK3,k3_tarski(sK1)) & ! [X3] : (r1_xboole_0(X3,sK3) | ~r2_hidden(X3,sK2)) & r1_tarski(sK3,k3_tarski(k2_xboole_0(sK1,sK2))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f10,plain,(
% 1.33/0.54    ? [X0,X1,X2] : (~r1_tarski(X2,k3_tarski(X0)) & ! [X3] : (r1_xboole_0(X3,X2) | ~r2_hidden(X3,X1)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))))),
% 1.33/0.54    inference(flattening,[],[f9])).
% 1.33/0.54  fof(f9,plain,(
% 1.33/0.54    ? [X0,X1,X2] : (~r1_tarski(X2,k3_tarski(X0)) & (! [X3] : (r1_xboole_0(X3,X2) | ~r2_hidden(X3,X1)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))))),
% 1.33/0.54    inference(ennf_transformation,[],[f7])).
% 1.33/0.54  fof(f7,negated_conjecture,(
% 1.33/0.54    ~! [X0,X1,X2] : ((! [X3] : (r2_hidden(X3,X1) => r1_xboole_0(X3,X2)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))) => r1_tarski(X2,k3_tarski(X0)))),
% 1.33/0.54    inference(negated_conjecture,[],[f6])).
% 1.33/0.54  fof(f6,conjecture,(
% 1.33/0.54    ! [X0,X1,X2] : ((! [X3] : (r2_hidden(X3,X1) => r1_xboole_0(X3,X2)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))) => r1_tarski(X2,k3_tarski(X0)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_setfam_1)).
% 1.33/0.54  fof(f228,plain,(
% 1.33/0.54    r1_tarski(sK3,k3_tarski(sK1))),
% 1.33/0.54    inference(duplicate_literal_removal,[],[f227])).
% 1.33/0.54  fof(f227,plain,(
% 1.33/0.54    r1_tarski(sK3,k3_tarski(sK1)) | r1_tarski(sK3,k3_tarski(sK1))),
% 1.33/0.54    inference(resolution,[],[f223,f42])).
% 1.33/0.54  fof(f42,plain,(
% 1.33/0.54    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f25])).
% 1.33/0.54  fof(f25,plain,(
% 1.33/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f24])).
% 1.33/0.54  fof(f24,plain,(
% 1.33/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f23,plain,(
% 1.33/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.33/0.54    inference(rectify,[],[f22])).
% 1.33/0.54  fof(f22,plain,(
% 1.33/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.33/0.54    inference(nnf_transformation,[],[f13])).
% 1.33/0.54  fof(f13,plain,(
% 1.33/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f1])).
% 1.33/0.54  fof(f1,axiom,(
% 1.33/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.33/0.54  fof(f223,plain,(
% 1.33/0.54    ( ! [X0] : (~r2_hidden(sK6(X0,k3_tarski(sK1)),sK3) | r1_tarski(X0,k3_tarski(sK1))) )),
% 1.33/0.54    inference(resolution,[],[f222,f43])).
% 1.33/0.54  fof(f43,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f25])).
% 1.33/0.54  fof(f222,plain,(
% 1.33/0.54    ( ! [X0] : (r2_hidden(X0,k3_tarski(sK1)) | ~r2_hidden(X0,sK3)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f213,f66])).
% 1.33/0.54  fof(f66,plain,(
% 1.33/0.54    ( ! [X0] : (~r2_hidden(X0,sK3) | ~r2_hidden(X0,k3_tarski(sK2))) )),
% 1.33/0.54    inference(resolution,[],[f65,f38])).
% 1.33/0.54  fof(f38,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f19])).
% 1.33/0.54  fof(f19,plain,(
% 1.33/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f18])).
% 1.33/0.54  fof(f18,plain,(
% 1.33/0.54    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f11,plain,(
% 1.33/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.33/0.54    inference(ennf_transformation,[],[f8])).
% 1.33/0.54  fof(f8,plain,(
% 1.33/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.33/0.54    inference(rectify,[],[f3])).
% 1.33/0.54  fof(f3,axiom,(
% 1.33/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.33/0.54  fof(f65,plain,(
% 1.33/0.54    r1_xboole_0(k3_tarski(sK2),sK3)),
% 1.33/0.54    inference(duplicate_literal_removal,[],[f64])).
% 1.33/0.54  fof(f64,plain,(
% 1.33/0.54    r1_xboole_0(k3_tarski(sK2),sK3) | r1_xboole_0(k3_tarski(sK2),sK3)),
% 1.33/0.54    inference(resolution,[],[f56,f39])).
% 1.33/0.54  fof(f39,plain,(
% 1.33/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(k3_tarski(X0),X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f21])).
% 1.33/0.54  fof(f21,plain,(
% 1.33/0.54    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | (~r1_xboole_0(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f20])).
% 1.33/0.54  fof(f20,plain,(
% 1.33/0.54    ! [X1,X0] : (? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)) => (~r1_xboole_0(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f12,plain,(
% 1.33/0.54    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f5])).
% 1.33/0.54  fof(f5,axiom,(
% 1.33/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_xboole_0(X2,X1)) => r1_xboole_0(k3_tarski(X0),X1))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).
% 1.33/0.54  fof(f56,plain,(
% 1.33/0.54    ( ! [X0] : (~r2_hidden(sK5(X0,sK3),sK2) | r1_xboole_0(k3_tarski(X0),sK3)) )),
% 1.33/0.54    inference(resolution,[],[f40,f33])).
% 1.33/0.54  fof(f33,plain,(
% 1.33/0.54    ( ! [X3] : (r1_xboole_0(X3,sK3) | ~r2_hidden(X3,sK2)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f17])).
% 1.33/0.54  fof(f40,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r1_xboole_0(sK5(X0,X1),X1) | r1_xboole_0(k3_tarski(X0),X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f21])).
% 1.33/0.54  fof(f213,plain,(
% 1.33/0.54    ( ! [X0] : (r2_hidden(X0,k3_tarski(sK1)) | r2_hidden(X0,k3_tarski(sK2)) | ~r2_hidden(X0,sK3)) )),
% 1.33/0.54    inference(resolution,[],[f137,f57])).
% 1.33/0.54  fof(f57,plain,(
% 1.33/0.54    ( ! [X0] : (r2_hidden(X0,k3_tarski(k2_xboole_0(sK1,sK2))) | ~r2_hidden(X0,sK3)) )),
% 1.33/0.54    inference(resolution,[],[f41,f32])).
% 1.33/0.54  fof(f32,plain,(
% 1.33/0.54    r1_tarski(sK3,k3_tarski(k2_xboole_0(sK1,sK2)))),
% 1.33/0.54    inference(cnf_transformation,[],[f17])).
% 1.33/0.54  fof(f41,plain,(
% 1.33/0.54    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f25])).
% 1.33/0.54  fof(f137,plain,(
% 1.33/0.54    ( ! [X4,X5,X3] : (~r2_hidden(X3,k3_tarski(k2_xboole_0(X4,X5))) | r2_hidden(X3,k3_tarski(X4)) | r2_hidden(X3,k3_tarski(X5))) )),
% 1.33/0.54    inference(resolution,[],[f44,f77])).
% 1.33/0.54  fof(f77,plain,(
% 1.33/0.54    ( ! [X0,X1] : (sP0(k3_tarski(X1),k3_tarski(X0),k3_tarski(k2_xboole_0(X0,X1)))) )),
% 1.33/0.54    inference(superposition,[],[f52,f35])).
% 1.33/0.54  fof(f35,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f4])).
% 1.33/0.54  fof(f4,axiom,(
% 1.33/0.54    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 1.33/0.54  fof(f52,plain,(
% 1.33/0.54    ( ! [X0,X1] : (sP0(X1,X0,k2_xboole_0(X0,X1))) )),
% 1.33/0.54    inference(equality_resolution,[],[f50])).
% 1.33/0.54  % (14016)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.54  fof(f50,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.33/0.54    inference(cnf_transformation,[],[f31])).
% 1.33/0.54  fof(f31,plain,(
% 1.33/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 1.33/0.54    inference(nnf_transformation,[],[f15])).
% 1.33/0.54  % (14031)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.33/0.54  fof(f15,plain,(
% 1.33/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.33/0.54    inference(definition_folding,[],[f2,f14])).
% 1.33/0.54  fof(f14,plain,(
% 1.33/0.54    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.33/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.33/0.54  fof(f2,axiom,(
% 1.33/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.33/0.54  fof(f44,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f30])).
% 1.33/0.54  fof(f30,plain,(
% 1.33/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK7(X0,X1,X2),X0) & ~r2_hidden(sK7(X0,X1,X2),X1)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).
% 1.33/0.54  % (14005)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.54  % (14003)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.54  fof(f29,plain,(
% 1.33/0.54    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK7(X0,X1,X2),X0) & ~r2_hidden(sK7(X0,X1,X2),X1)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f28,plain,(
% 1.33/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.33/0.54    inference(rectify,[],[f27])).
% 1.33/0.54  fof(f27,plain,(
% 1.33/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.33/0.54    inference(flattening,[],[f26])).
% 1.33/0.54  fof(f26,plain,(
% 1.33/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.33/0.54    inference(nnf_transformation,[],[f14])).
% 1.33/0.54  % SZS output end Proof for theBenchmark
% 1.33/0.54  % (14009)------------------------------
% 1.33/0.54  % (14009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (14009)Termination reason: Refutation
% 1.33/0.54  
% 1.33/0.54  % (14009)Memory used [KB]: 6524
% 1.33/0.54  % (14009)Time elapsed: 0.079 s
% 1.33/0.54  % (14009)------------------------------
% 1.33/0.54  % (14009)------------------------------
% 1.33/0.54  % (14006)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.33/0.55  % (14001)Success in time 0.184 s
%------------------------------------------------------------------------------
