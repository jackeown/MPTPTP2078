%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 128 expanded)
%              Number of leaves         :   12 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  195 ( 462 expanded)
%              Number of equality atoms :   53 ( 167 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(subsumption_resolution,[],[f141,f83])).

fof(f83,plain,(
    k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f28,f80])).

fof(f80,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK2) ),
    inference(resolution,[],[f79,f27])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

% (13912)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f16,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f15])).

% (13909)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f15,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

% (13937)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f78,f51])).

fof(f51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f50,f27])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f41,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f68,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f10,f13,f12])).

fof(f12,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3,X4] :
          ( r2_hidden(k4_tarski(X3,X4),X2)
        <=> ? [X5] :
              ( r2_hidden(k4_tarski(X5,X4),X1)
              & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ( k5_relat_1(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f68,plain,(
    ! [X0] :
      ( ~ sP1(k1_xboole_0,k1_xboole_0,X0)
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f67,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,X1,X0)
      | k5_relat_1(X1,X2) = X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( k5_relat_1(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k5_relat_1(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ( ( k5_relat_1(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k5_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X13] : sP0(X13,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f59,f48])).

fof(f48,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f39,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f59,plain,(
    ! [X17,X16] :
      ( r2_hidden(k4_tarski(sK3(X16,k1_xboole_0,X17),sK4(X16,k1_xboole_0,X17)),X17)
      | sP0(X16,k1_xboole_0,X17) ) ),
    inference(resolution,[],[f35,f48])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0)
                | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X1) )
            | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
          & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X1) )
            | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
      & ( ! [X7,X8] :
            ( ( r2_hidden(k4_tarski(X7,X8),X2)
              | ! [X9] :
                  ( ~ r2_hidden(k4_tarski(X9,X8),X0)
                  | ~ r2_hidden(k4_tarski(X7,X9),X1) ) )
            & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X0)
                & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X1) )
              | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X0)
                | ~ r2_hidden(k4_tarski(X3,X5),X1) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X0)
                & r2_hidden(k4_tarski(X3,X6),X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X1) )
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X0)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X1) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X0)
          & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X1) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X0)
          & r2_hidden(k4_tarski(X7,X10),X1) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X0)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(k4_tarski(X5,X4),X0)
                  | ~ r2_hidden(k4_tarski(X3,X5),X1) )
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ? [X6] :
                  ( r2_hidden(k4_tarski(X6,X4),X0)
                  & r2_hidden(k4_tarski(X3,X6),X1) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X7,X8] :
            ( ( r2_hidden(k4_tarski(X7,X8),X2)
              | ! [X9] :
                  ( ~ r2_hidden(k4_tarski(X9,X8),X0)
                  | ~ r2_hidden(k4_tarski(X7,X9),X1) ) )
            & ( ? [X10] :
                  ( r2_hidden(k4_tarski(X10,X8),X0)
                  & r2_hidden(k4_tarski(X7,X10),X1) )
              | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3,X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                  | ~ r2_hidden(k4_tarski(X3,X5),X0) )
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(k4_tarski(X3,X5),X0) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X2)
              | ! [X5] :
                  ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                  | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(k4_tarski(X3,X5),X0) )
              | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f28,plain,
    ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f141,plain,(
    k1_xboole_0 = k5_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f140,f27])).

fof(f140,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f139,f51])).

fof(f139,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f137,f38])).

fof(f137,plain,(
    ! [X0] :
      ( ~ sP1(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f136,f31])).

fof(f136,plain,(
    ! [X13] : sP0(k1_xboole_0,X13,k1_xboole_0) ),
    inference(resolution,[],[f72,f48])).

fof(f72,plain,(
    ! [X17,X16] :
      ( r2_hidden(k4_tarski(sK3(k1_xboole_0,X16,X17),sK4(k1_xboole_0,X16,X17)),X17)
      | sP0(k1_xboole_0,X16,X17) ) ),
    inference(resolution,[],[f36,f48])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:30:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (13916)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (13916)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (13935)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.51  % (13911)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (13911)Refutation not found, incomplete strategy% (13911)------------------------------
% 0.22/0.51  % (13911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13932)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (13913)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (13927)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.51  % (13911)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13911)Memory used [KB]: 10618
% 0.22/0.51  % (13911)Time elapsed: 0.096 s
% 0.22/0.51  % (13911)------------------------------
% 0.22/0.51  % (13911)------------------------------
% 0.22/0.51  % (13914)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (13924)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (13931)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (13931)Refutation not found, incomplete strategy% (13931)------------------------------
% 0.22/0.52  % (13931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13931)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13931)Memory used [KB]: 10746
% 0.22/0.52  % (13931)Time elapsed: 0.077 s
% 0.22/0.52  % (13931)------------------------------
% 0.22/0.52  % (13931)------------------------------
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f141,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f28,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK2)),
% 0.22/0.52    inference(resolution,[],[f79,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  % (13912)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    (k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)) & v1_relat_1(sK2)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f15])).
% 0.22/0.52  % (13909)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)) & v1_relat_1(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  % (13937)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.52  fof(f8,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f7])).
% 0.22/0.52  fof(f7,conjecture,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f78,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    v1_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(resolution,[],[f50,f27])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k1_xboole_0)) )),
% 0.22/0.52    inference(superposition,[],[f41,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.52    inference(resolution,[],[f68,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP1(X2,X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(definition_folding,[],[f10,f13,f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0))))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X2,X0,X1] : ((k5_relat_1(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X0] : (~sP1(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(resolution,[],[f67,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~sP0(X2,X1,X0) | k5_relat_1(X1,X2) = X0 | ~sP1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((k5_relat_1(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k5_relat_1(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 0.22/0.52    inference(rectify,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X2,X0,X1] : (((k5_relat_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k5_relat_1(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f13])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X13] : (sP0(X13,k1_xboole_0,k1_xboole_0)) )),
% 0.22/0.52    inference(resolution,[],[f59,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(superposition,[],[f39,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.52    inference(flattening,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X17,X16] : (r2_hidden(k4_tarski(sK3(X16,k1_xboole_0,X17),sK4(X16,k1_xboole_0,X17)),X17) | sP0(X16,k1_xboole_0,X17)) )),
% 0.22/0.52    inference(resolution,[],[f35,f48])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | sP0(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X0) | ~r2_hidden(k4_tarski(X7,X9),X1))) & ((r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X0) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X1)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f20,f23,f22,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X3,X5),X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X0) & r2_hidden(k4_tarski(X3,X6),X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X1)) => (r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X1)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X0) & r2_hidden(k4_tarski(X7,X10),X1)) => (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X0) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X1)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X3,X5),X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X0) & r2_hidden(k4_tarski(X3,X6),X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X0) | ~r2_hidden(k4_tarski(X7,X9),X1))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X0) & r2_hidden(k4_tarski(X7,X10),X1)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.52    inference(rectify,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.52    inference(nnf_transformation,[],[f12])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    k1_xboole_0 = k5_relat_1(sK2,k1_xboole_0)),
% 0.22/0.52    inference(resolution,[],[f140,f27])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f139,f51])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f138])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(resolution,[],[f137,f38])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ( ! [X0] : (~sP1(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(resolution,[],[f136,f31])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    ( ! [X13] : (sP0(k1_xboole_0,X13,k1_xboole_0)) )),
% 0.22/0.52    inference(resolution,[],[f72,f48])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X17,X16] : (r2_hidden(k4_tarski(sK3(k1_xboole_0,X16,X17),sK4(k1_xboole_0,X16,X17)),X17) | sP0(k1_xboole_0,X16,X17)) )),
% 0.22/0.52    inference(resolution,[],[f36,f48])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | sP0(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (13916)------------------------------
% 0.22/0.52  % (13916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13916)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (13916)Memory used [KB]: 6396
% 0.22/0.52  % (13916)Time elapsed: 0.092 s
% 0.22/0.52  % (13916)------------------------------
% 0.22/0.52  % (13916)------------------------------
% 0.22/0.52  % (13908)Success in time 0.161 s
%------------------------------------------------------------------------------
