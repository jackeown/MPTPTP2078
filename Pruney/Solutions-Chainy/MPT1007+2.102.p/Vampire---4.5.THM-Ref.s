%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 (  76 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :  195 ( 343 expanded)
%              Number of equality atoms :   63 (  95 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(subsumption_resolution,[],[f135,f30])).

fof(f30,plain,(
    ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f135,plain,(
    r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(resolution,[],[f134,f77])).

fof(f77,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f72,f46])).

fof(f46,plain,(
    ! [X4,X2,X3,X1] : sP0(X1,X1,X2,X3,X4) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( ( sP0(X5,X3,X2,X1,X0)
        | ( X3 != X5
          & X2 != X5
          & X1 != X5
          & X0 != X5 ) )
      & ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5
        | ~ sP0(X5,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( ( sP0(X5,X3,X2,X1,X0)
        | ( X3 != X5
          & X2 != X5
          & X1 != X5
          & X0 != X5 ) )
      & ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5
        | ~ sP0(X5,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( sP0(X5,X3,X2,X1,X0)
    <=> ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f72,plain,(
    ! [X12,X13] :
      ( ~ sP0(X12,X13,X13,X13,X13)
      | r2_hidden(X12,k1_tarski(X13)) ) ),
    inference(resolution,[],[f36,f53])).

fof(f53,plain,(
    ! [X0] : sP1(X0,X0,X0,X0,k1_tarski(X0)) ),
    inference(superposition,[],[f52,f31])).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : sP1(X0,X0,X0,X1,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f51,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : sP1(X0,X0,X1,X2,k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f50,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : sP1(X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP1(X0,X1,X2,X3,X4) )
      & ( sP1(X0,X1,X2,X3,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP1(X0,X1,X2,X3,X4) ) ),
    inference(definition_folding,[],[f12,f14,f13])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP1(X0,X1,X2,X3,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> sP0(X5,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | ~ sP0(X6,X3,X2,X1,X0)
      | r2_hidden(X6,X4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ( ( ~ sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4),X4) )
          & ( sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ~ sP0(X6,X3,X2,X1,X0) )
            & ( sP0(X6,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f20])).

fof(f20,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ sP0(X5,X3,X2,X1,X0)
            | ~ r2_hidden(X5,X4) )
          & ( sP0(X5,X3,X2,X1,X0)
            | r2_hidden(X5,X4) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4),X4) )
        & ( sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ~ sP0(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) )
            & ( sP0(X5,X3,X2,X1,X0)
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ~ sP0(X6,X3,X2,X1,X0) )
            & ( sP0(X6,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ~ sP0(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) )
            & ( sP0(X5,X3,X2,X1,X0)
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ~ sP0(X5,X3,X2,X1,X0) )
            & ( sP0(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK2))
      | r2_hidden(k1_funct_1(sK4,X0),sK3) ) ),
    inference(subsumption_resolution,[],[f133,f27])).

fof(f27,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK2))
      | ~ v1_funct_2(sK4,k1_tarski(sK2),sK3)
      | r2_hidden(k1_funct_1(sK4,X0),sK3) ) ),
    inference(subsumption_resolution,[],[f132,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK2))
      | k1_xboole_0 = sK3
      | ~ v1_funct_2(sK4,k1_tarski(sK2),sK3)
      | r2_hidden(k1_funct_1(sK4,X0),sK3) ) ),
    inference(resolution,[],[f131,f28])).

fof(f28,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f17])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK4,X2,X0)
      | r2_hidden(k1_funct_1(sK4,X1),X0) ) ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:38:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (25222)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (25226)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (25229)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (25229)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (25250)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (25224)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (25249)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (25223)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (25237)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (25228)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (25227)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (25238)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f135,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ~r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f8])).
% 0.22/0.54  fof(f8,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.22/0.54    inference(negated_conjecture,[],[f6])).
% 0.22/0.54  fof(f6,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 0.22/0.54    inference(resolution,[],[f134,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.22/0.54    inference(resolution,[],[f72,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X4,X2,X3,X1] : (sP0(X1,X1,X2,X3,X4)) )),
% 0.22/0.54    inference(equality_resolution,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | ~sP0(X0,X1,X2,X3,X4)))),
% 0.22/0.54    inference(rectify,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X5,X3,X2,X1,X0] : ((sP0(X5,X3,X2,X1,X0) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~sP0(X5,X3,X2,X1,X0)))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X5,X3,X2,X1,X0] : ((sP0(X5,X3,X2,X1,X0) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~sP0(X5,X3,X2,X1,X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X5,X3,X2,X1,X0] : (sP0(X5,X3,X2,X1,X0) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X12,X13] : (~sP0(X12,X13,X13,X13,X13) | r2_hidden(X12,k1_tarski(X13))) )),
% 0.22/0.54    inference(resolution,[],[f36,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0] : (sP1(X0,X0,X0,X0,k1_tarski(X0))) )),
% 0.22/0.54    inference(superposition,[],[f52,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sP1(X0,X0,X0,X1,k2_tarski(X0,X1))) )),
% 0.22/0.54    inference(superposition,[],[f51,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sP1(X0,X0,X1,X2,k1_enumset1(X0,X1,X2))) )),
% 0.22/0.54    inference(superposition,[],[f50,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3))) )),
% 0.22/0.54    inference(equality_resolution,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP1(X0,X1,X2,X3,X4)) & (sP1(X0,X1,X2,X3,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.54    inference(nnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP1(X0,X1,X2,X3,X4))),
% 0.22/0.54    inference(definition_folding,[],[f12,f14,f13])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : (sP1(X0,X1,X2,X3,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> sP0(X5,X3,X2,X1,X0)))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3,X4) | ~sP0(X6,X3,X2,X1,X0) | r2_hidden(X6,X4)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ((~sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4),X4)) & (sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | ~sP0(X6,X3,X2,X1,X0)) & (sP0(X6,X3,X2,X1,X0) | ~r2_hidden(X6,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X4,X3,X2,X1,X0] : (? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4))) => ((~sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4),X4)) & (sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4),X4))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | ~sP0(X6,X3,X2,X1,X0)) & (sP0(X6,X3,X2,X1,X0) | ~r2_hidden(X6,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 0.22/0.54    inference(rectify,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | ~sP0(X5,X3,X2,X1,X0)) & (sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 0.22/0.54    inference(nnf_transformation,[],[f14])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK2)) | r2_hidden(k1_funct_1(sK4,X0),sK3)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f133,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK2)) | ~v1_funct_2(sK4,k1_tarski(sK2),sK3) | r2_hidden(k1_funct_1(sK4,X0),sK3)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f132,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    k1_xboole_0 != sK3),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK2)) | k1_xboole_0 = sK3 | ~v1_funct_2(sK4,k1_tarski(sK2),sK3) | r2_hidden(k1_funct_1(sK4,X0),sK3)) )),
% 0.22/0.54    inference(resolution,[],[f131,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~v1_funct_2(sK4,X2,X0) | r2_hidden(k1_funct_1(sK4,X1),X0)) )),
% 0.22/0.54    inference(resolution,[],[f34,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    v1_funct_1(sK4)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.54    inference(flattening,[],[f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (25229)------------------------------
% 0.22/0.54  % (25229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25229)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (25229)Memory used [KB]: 6268
% 0.22/0.54  % (25229)Time elapsed: 0.116 s
% 0.22/0.54  % (25229)------------------------------
% 0.22/0.54  % (25229)------------------------------
% 0.22/0.54  % (25235)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (25219)Success in time 0.173 s
%------------------------------------------------------------------------------
