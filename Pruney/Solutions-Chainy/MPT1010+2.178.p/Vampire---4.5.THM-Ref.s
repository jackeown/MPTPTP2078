%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 236 expanded)
%              Number of leaves         :   19 (  74 expanded)
%              Depth                    :   17
%              Number of atoms          :  246 ( 522 expanded)
%              Number of equality atoms :  112 ( 272 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f167,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f39,f40,f166])).

fof(f166,plain,(
    ! [X0] :
      ( sK3 = k1_funct_1(sK5,X0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | sK3 = k1_funct_1(sK5,X0)
      | sK3 = k1_funct_1(sK5,X0)
      | sK3 = k1_funct_1(sK5,X0)
      | sK3 = k1_funct_1(sK5,X0) ) ),
    inference(resolution,[],[f155,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( sP0(X5,X3,X2,X1,X0)
    <=> ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f155,plain,(
    ! [X8] :
      ( sP0(k1_funct_1(sK5,X8),sK3,sK3,sK3,sK3)
      | ~ r2_hidden(X8,sK2) ) ),
    inference(subsumption_resolution,[],[f145,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f145,plain,(
    ! [X8] :
      ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(X8,sK2)
      | sP0(k1_funct_1(sK5,X8),sK3,sK3,sK3,sK3) ) ),
    inference(superposition,[],[f107,f119])).

fof(f119,plain,(
    ! [X0] :
      ( k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
      | ~ r2_hidden(X0,sK2)
      | sP0(k1_funct_1(sK5,X0),sK3,sK3,sK3,sK3) ) ),
    inference(resolution,[],[f101,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4))
      | sP0(X0,X4,X3,X2,X1) ) ),
    inference(resolution,[],[f53,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : sP1(X0,X1,X2,X3,k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) != X4 ) ),
    inference(definition_unfolding,[],[f62,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP1(X0,X1,X2,X3,X4) )
      & ( sP1(X0,X1,X2,X3,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP1(X0,X1,X2,X3,X4) ) ),
    inference(definition_folding,[],[f21,f23,f22])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP1(X0,X1,X2,X3,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> sP0(X5,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | ~ r2_hidden(X6,X4)
      | sP0(X6,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ( ( ~ sP0(sK6(X0,X1,X2,X3,X4),X3,X2,X1,X0)
            | ~ r2_hidden(sK6(X0,X1,X2,X3,X4),X4) )
          & ( sP0(sK6(X0,X1,X2,X3,X4),X3,X2,X1,X0)
            | r2_hidden(sK6(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ~ sP0(X6,X3,X2,X1,X0) )
            & ( sP0(X6,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f29,f30])).

fof(f30,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ sP0(X5,X3,X2,X1,X0)
            | ~ r2_hidden(X5,X4) )
          & ( sP0(X5,X3,X2,X1,X0)
            | r2_hidden(X5,X4) ) )
     => ( ( ~ sP0(sK6(X0,X1,X2,X3,X4),X3,X2,X1,X0)
          | ~ r2_hidden(sK6(X0,X1,X2,X3,X4),X4) )
        & ( sP0(sK6(X0,X1,X2,X3,X4),X3,X2,X1,X0)
          | r2_hidden(sK6(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f101,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK5,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
      | ~ r2_hidden(X0,sK2)
      | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ) ),
    inference(subsumption_resolution,[],[f100,f36])).

fof(f36,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK3 != k1_funct_1(sK5,sK4)
    & r2_hidden(sK4,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK3 != k1_funct_1(sK5,sK4)
      & r2_hidden(sK4,sK2)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_2(sK5,sK2,k1_tarski(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

% (12765)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f100,plain,(
    ! [X0] :
      ( k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
      | ~ r2_hidden(X0,sK2)
      | r2_hidden(k1_funct_1(sK5,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f99,f75])).

fof(f75,plain,(
    v1_funct_2(sK5,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f37,f73])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f68])).

% (12744)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    ! [X0] :
      ( k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
      | ~ r2_hidden(X0,sK2)
      | r2_hidden(k1_funct_1(sK5,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
      | ~ v1_funct_2(sK5,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f51,f74])).

fof(f74,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f38,f73])).

fof(f38,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f107,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f81,f76])).

fof(f76,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f73])).

fof(f41,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f81,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f47,f73,f72,f73,f73])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f70])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f40,plain,(
    sK3 != k1_funct_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:42:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (12763)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (12755)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (12771)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (12756)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (12750)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (12747)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (12771)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (12764)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (12748)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (12756)Refutation not found, incomplete strategy% (12756)------------------------------
% 0.20/0.52  % (12756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (12756)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (12756)Memory used [KB]: 6268
% 0.20/0.53  % (12756)Time elapsed: 0.096 s
% 0.20/0.53  % (12756)------------------------------
% 0.20/0.53  % (12756)------------------------------
% 0.20/0.53  % (12741)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (12764)Refutation not found, incomplete strategy% (12764)------------------------------
% 0.20/0.53  % (12764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (12764)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (12764)Memory used [KB]: 1791
% 0.20/0.53  % (12764)Time elapsed: 0.105 s
% 0.20/0.53  % (12764)------------------------------
% 0.20/0.53  % (12764)------------------------------
% 1.33/0.53  % SZS output start Proof for theBenchmark
% 1.33/0.53  fof(f167,plain,(
% 1.33/0.53    $false),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f39,f40,f166])).
% 1.33/0.53  fof(f166,plain,(
% 1.33/0.53    ( ! [X0] : (sK3 = k1_funct_1(sK5,X0) | ~r2_hidden(X0,sK2)) )),
% 1.33/0.53    inference(duplicate_literal_removal,[],[f165])).
% 1.33/0.53  fof(f165,plain,(
% 1.33/0.53    ( ! [X0] : (~r2_hidden(X0,sK2) | sK3 = k1_funct_1(sK5,X0) | sK3 = k1_funct_1(sK5,X0) | sK3 = k1_funct_1(sK5,X0) | sK3 = k1_funct_1(sK5,X0)) )),
% 1.33/0.53    inference(resolution,[],[f155,f57])).
% 1.33/0.53  fof(f57,plain,(
% 1.33/0.53    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X1) )),
% 1.33/0.53    inference(cnf_transformation,[],[f34])).
% 1.33/0.53  fof(f34,plain,(
% 1.33/0.53    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | ~sP0(X0,X1,X2,X3,X4)))),
% 1.33/0.53    inference(rectify,[],[f33])).
% 1.33/0.53  fof(f33,plain,(
% 1.33/0.53    ! [X5,X3,X2,X1,X0] : ((sP0(X5,X3,X2,X1,X0) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~sP0(X5,X3,X2,X1,X0)))),
% 1.33/0.53    inference(flattening,[],[f32])).
% 1.33/0.53  fof(f32,plain,(
% 1.33/0.53    ! [X5,X3,X2,X1,X0] : ((sP0(X5,X3,X2,X1,X0) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~sP0(X5,X3,X2,X1,X0)))),
% 1.33/0.53    inference(nnf_transformation,[],[f22])).
% 1.33/0.53  fof(f22,plain,(
% 1.33/0.53    ! [X5,X3,X2,X1,X0] : (sP0(X5,X3,X2,X1,X0) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5))),
% 1.33/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.33/0.53  fof(f155,plain,(
% 1.33/0.53    ( ! [X8] : (sP0(k1_funct_1(sK5,X8),sK3,sK3,sK3,sK3) | ~r2_hidden(X8,sK2)) )),
% 1.33/0.53    inference(subsumption_resolution,[],[f145,f42])).
% 1.33/0.53  fof(f42,plain,(
% 1.33/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.33/0.53    inference(cnf_transformation,[],[f2])).
% 1.33/0.53  fof(f2,axiom,(
% 1.33/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.33/0.53  fof(f145,plain,(
% 1.33/0.53    ( ! [X8] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~r2_hidden(X8,sK2) | sP0(k1_funct_1(sK5,X8),sK3,sK3,sK3,sK3)) )),
% 1.33/0.53    inference(superposition,[],[f107,f119])).
% 1.33/0.53  fof(f119,plain,(
% 1.33/0.53    ( ! [X0] : (k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~r2_hidden(X0,sK2) | sP0(k1_funct_1(sK5,X0),sK3,sK3,sK3,sK3)) )),
% 1.33/0.53    inference(resolution,[],[f101,f87])).
% 1.33/0.53  fof(f87,plain,(
% 1.33/0.53    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)) | sP0(X0,X4,X3,X2,X1)) )),
% 1.33/0.53    inference(resolution,[],[f53,f86])).
% 1.33/0.53  fof(f86,plain,(
% 1.33/0.53    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3))) )),
% 1.33/0.53    inference(equality_resolution,[],[f80])).
% 1.33/0.53  fof(f80,plain,(
% 1.33/0.53    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) != X4) )),
% 1.33/0.53    inference(definition_unfolding,[],[f62,f68])).
% 1.33/0.53  fof(f68,plain,(
% 1.33/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.33/0.53    inference(definition_unfolding,[],[f50,f67])).
% 1.33/0.53  fof(f67,plain,(
% 1.33/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.33/0.53    inference(definition_unfolding,[],[f52,f66])).
% 1.33/0.53  fof(f66,plain,(
% 1.33/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.33/0.53    inference(definition_unfolding,[],[f64,f65])).
% 1.33/0.53  fof(f65,plain,(
% 1.33/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f9])).
% 1.33/0.53  fof(f9,axiom,(
% 1.33/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.33/0.53  fof(f64,plain,(
% 1.33/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f8])).
% 1.33/0.53  fof(f8,axiom,(
% 1.33/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.33/0.53  fof(f52,plain,(
% 1.33/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f7])).
% 1.33/0.53  fof(f7,axiom,(
% 1.33/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.33/0.53  fof(f50,plain,(
% 1.33/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f6])).
% 1.33/0.53  fof(f6,axiom,(
% 1.33/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.33/0.53  fof(f62,plain,(
% 1.33/0.53    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 1.33/0.53    inference(cnf_transformation,[],[f35])).
% 1.33/0.53  fof(f35,plain,(
% 1.33/0.53    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP1(X0,X1,X2,X3,X4)) & (sP1(X0,X1,X2,X3,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 1.33/0.53    inference(nnf_transformation,[],[f24])).
% 1.33/0.53  fof(f24,plain,(
% 1.33/0.53    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP1(X0,X1,X2,X3,X4))),
% 1.33/0.53    inference(definition_folding,[],[f21,f23,f22])).
% 1.33/0.53  fof(f23,plain,(
% 1.33/0.53    ! [X0,X1,X2,X3,X4] : (sP1(X0,X1,X2,X3,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> sP0(X5,X3,X2,X1,X0)))),
% 1.33/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.33/0.53  fof(f21,plain,(
% 1.33/0.53    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 1.33/0.53    inference(ennf_transformation,[],[f11])).
% 1.33/0.53  fof(f11,axiom,(
% 1.33/0.53    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).
% 1.33/0.53  fof(f53,plain,(
% 1.33/0.53    ( ! [X6,X4,X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3,X4) | ~r2_hidden(X6,X4) | sP0(X6,X3,X2,X1,X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f31])).
% 1.33/0.53  fof(f31,plain,(
% 1.33/0.53    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ((~sP0(sK6(X0,X1,X2,X3,X4),X3,X2,X1,X0) | ~r2_hidden(sK6(X0,X1,X2,X3,X4),X4)) & (sP0(sK6(X0,X1,X2,X3,X4),X3,X2,X1,X0) | r2_hidden(sK6(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | ~sP0(X6,X3,X2,X1,X0)) & (sP0(X6,X3,X2,X1,X0) | ~r2_hidden(X6,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 1.33/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f29,f30])).
% 1.33/0.53  fof(f30,plain,(
% 1.33/0.53    ! [X4,X3,X2,X1,X0] : (? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4))) => ((~sP0(sK6(X0,X1,X2,X3,X4),X3,X2,X1,X0) | ~r2_hidden(sK6(X0,X1,X2,X3,X4),X4)) & (sP0(sK6(X0,X1,X2,X3,X4),X3,X2,X1,X0) | r2_hidden(sK6(X0,X1,X2,X3,X4),X4))))),
% 1.33/0.53    introduced(choice_axiom,[])).
% 1.33/0.53  fof(f29,plain,(
% 1.33/0.53    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | ~sP0(X6,X3,X2,X1,X0)) & (sP0(X6,X3,X2,X1,X0) | ~r2_hidden(X6,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 1.33/0.53    inference(rectify,[],[f28])).
% 1.33/0.53  fof(f28,plain,(
% 1.33/0.53    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | ~sP0(X5,X3,X2,X1,X0)) & (sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 1.33/0.53    inference(nnf_transformation,[],[f23])).
% 1.33/0.53  fof(f101,plain,(
% 1.33/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK5,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(X0,sK2) | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) )),
% 1.33/0.53    inference(subsumption_resolution,[],[f100,f36])).
% 1.33/0.53  fof(f36,plain,(
% 1.33/0.53    v1_funct_1(sK5)),
% 1.33/0.53    inference(cnf_transformation,[],[f26])).
% 1.33/0.53  fof(f26,plain,(
% 1.33/0.53    sK3 != k1_funct_1(sK5,sK4) & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)),
% 1.33/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f25])).
% 1.33/0.53  fof(f25,plain,(
% 1.33/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK3 != k1_funct_1(sK5,sK4) & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 1.33/0.53    introduced(choice_axiom,[])).
% 1.33/0.53  fof(f18,plain,(
% 1.33/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.33/0.53    inference(flattening,[],[f17])).
% 1.33/0.53  fof(f17,plain,(
% 1.33/0.53    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.33/0.53    inference(ennf_transformation,[],[f16])).
% 1.33/0.53  fof(f16,negated_conjecture,(
% 1.33/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.33/0.53    inference(negated_conjecture,[],[f15])).
% 1.33/0.53  % (12765)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.53  fof(f15,conjecture,(
% 1.33/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 1.33/0.53  fof(f100,plain,(
% 1.33/0.53    ( ! [X0] : (k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~r2_hidden(X0,sK2) | r2_hidden(k1_funct_1(sK5,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~v1_funct_1(sK5)) )),
% 1.33/0.53    inference(subsumption_resolution,[],[f99,f75])).
% 1.33/0.53  fof(f75,plain,(
% 1.33/0.53    v1_funct_2(sK5,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),
% 1.33/0.53    inference(definition_unfolding,[],[f37,f73])).
% 1.33/0.53  fof(f73,plain,(
% 1.33/0.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.33/0.53    inference(definition_unfolding,[],[f43,f70])).
% 1.33/0.53  fof(f70,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.33/0.53    inference(definition_unfolding,[],[f45,f69])).
% 1.33/0.53  fof(f69,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.33/0.53    inference(definition_unfolding,[],[f49,f68])).
% 1.33/0.53  % (12744)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.53  fof(f49,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f5])).
% 1.33/0.53  fof(f5,axiom,(
% 1.33/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.33/0.53  fof(f45,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f4])).
% 1.33/0.53  fof(f4,axiom,(
% 1.33/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.33/0.53  fof(f43,plain,(
% 1.33/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f3])).
% 1.33/0.53  fof(f3,axiom,(
% 1.33/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.33/0.53  fof(f37,plain,(
% 1.33/0.53    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 1.33/0.53    inference(cnf_transformation,[],[f26])).
% 1.33/0.53  fof(f99,plain,(
% 1.33/0.53    ( ! [X0] : (k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~r2_hidden(X0,sK2) | r2_hidden(k1_funct_1(sK5,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~v1_funct_2(sK5,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~v1_funct_1(sK5)) )),
% 1.33/0.53    inference(resolution,[],[f51,f74])).
% 1.33/0.53  fof(f74,plain,(
% 1.33/0.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))),
% 1.33/0.53    inference(definition_unfolding,[],[f38,f73])).
% 1.33/0.53  fof(f38,plain,(
% 1.33/0.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 1.33/0.53    inference(cnf_transformation,[],[f26])).
% 1.33/0.53  fof(f51,plain,(
% 1.33/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f20])).
% 1.33/0.53  fof(f20,plain,(
% 1.33/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.33/0.53    inference(flattening,[],[f19])).
% 1.33/0.53  fof(f19,plain,(
% 1.33/0.53    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.33/0.53    inference(ennf_transformation,[],[f14])).
% 1.33/0.53  fof(f14,axiom,(
% 1.33/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 1.33/0.53  fof(f107,plain,(
% 1.33/0.53    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 1.33/0.53    inference(forward_demodulation,[],[f81,f76])).
% 1.33/0.53  fof(f76,plain,(
% 1.33/0.53    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.33/0.53    inference(definition_unfolding,[],[f41,f73])).
% 1.33/0.53  fof(f41,plain,(
% 1.33/0.53    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.33/0.53    inference(cnf_transformation,[],[f12])).
% 1.33/0.53  fof(f12,axiom,(
% 1.33/0.53    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.33/0.53  fof(f81,plain,(
% 1.33/0.53    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.33/0.53    inference(equality_resolution,[],[f78])).
% 1.33/0.53  fof(f78,plain,(
% 1.33/0.53    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.33/0.53    inference(definition_unfolding,[],[f47,f73,f72,f73,f73])).
% 1.33/0.53  fof(f72,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.33/0.53    inference(definition_unfolding,[],[f46,f71])).
% 1.33/0.53  fof(f71,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.33/0.53    inference(definition_unfolding,[],[f44,f70])).
% 1.33/0.53  fof(f44,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.33/0.53    inference(cnf_transformation,[],[f13])).
% 1.33/0.53  fof(f13,axiom,(
% 1.33/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.33/0.53  fof(f46,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.33/0.53    inference(cnf_transformation,[],[f1])).
% 1.33/0.53  fof(f1,axiom,(
% 1.33/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.33/0.53  fof(f47,plain,(
% 1.33/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.33/0.53    inference(cnf_transformation,[],[f27])).
% 1.33/0.53  fof(f27,plain,(
% 1.33/0.53    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.33/0.53    inference(nnf_transformation,[],[f10])).
% 1.33/0.53  fof(f10,axiom,(
% 1.33/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.33/0.53  fof(f40,plain,(
% 1.33/0.53    sK3 != k1_funct_1(sK5,sK4)),
% 1.33/0.53    inference(cnf_transformation,[],[f26])).
% 1.33/0.53  fof(f39,plain,(
% 1.33/0.53    r2_hidden(sK4,sK2)),
% 1.33/0.53    inference(cnf_transformation,[],[f26])).
% 1.33/0.53  % SZS output end Proof for theBenchmark
% 1.33/0.53  % (12771)------------------------------
% 1.33/0.53  % (12771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (12771)Termination reason: Refutation
% 1.33/0.53  
% 1.33/0.53  % (12771)Memory used [KB]: 1791
% 1.33/0.53  % (12771)Time elapsed: 0.104 s
% 1.33/0.53  % (12771)------------------------------
% 1.33/0.53  % (12771)------------------------------
% 1.33/0.53  % (12743)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.53  % (12740)Success in time 0.175 s
%------------------------------------------------------------------------------
