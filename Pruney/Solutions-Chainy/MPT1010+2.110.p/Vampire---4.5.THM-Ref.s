%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 (  88 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  240 ( 385 expanded)
%              Number of equality atoms :  112 ( 143 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(subsumption_resolution,[],[f130,f40])).

fof(f40,plain,(
    sK2 != k1_funct_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK2 != k1_funct_1(sK4,sK3)
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK2 != k1_funct_1(sK4,sK3)
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_2(sK4,sK1,k1_tarski(sK2))
      & v1_funct_1(sK4) ) ),
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f130,plain,(
    sK2 = k1_funct_1(sK4,sK3) ),
    inference(resolution,[],[f129,f39])).

fof(f39,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f129,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK2 = k1_funct_1(sK4,X0) ) ),
    inference(resolution,[],[f128,f111])).

fof(f111,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,k1_tarski(X7))
      | X7 = X8 ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X8,X7] :
      ( X7 = X8
      | X7 = X8
      | ~ r2_hidden(X8,k1_tarski(X7))
      | X7 = X8 ) ),
    inference(resolution,[],[f51,f95])).

fof(f95,plain,(
    ! [X0] : sP0(X0,X0,X0,k1_tarski(X0)) ),
    inference(superposition,[],[f86,f41])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f86,plain,(
    ! [X0,X1] : sP0(X1,X0,X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f65,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK6(X0,X1,X2,X3) != X0
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X0
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X2
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK6(X0,X1,X2,X3) != X0
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X0
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X2
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f128,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f127,f37])).

fof(f37,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_funct_2(sK4,sK1,k1_tarski(sK2))
      | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2)) ) ),
    inference(subsumption_resolution,[],[f126,f81])).

fof(f81,plain,(
    ! [X2] : k1_xboole_0 != k1_tarski(X2) ),
    inference(superposition,[],[f69,f75])).

fof(f75,plain,(
    ! [X0] : k2_xboole_0(sK5(X0),X0) = X0 ),
    inference(resolution,[],[f46,f73])).

fof(f73,plain,(
    ! [X0] : r1_tarski(sK5(X0),X0) ),
    inference(resolution,[],[f47,f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0)) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(X1,k1_tarski(X0)) ),
    inference(superposition,[],[f43,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f126,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = k1_tarski(sK2)
      | ~ v1_funct_2(sK4,sK1,k1_tarski(sK2))
      | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2)) ) ),
    inference(resolution,[],[f125,f38])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK4,X2,X0)
      | r2_hidden(k1_funct_1(sK4,X1),X0) ) ),
    inference(resolution,[],[f50,f36])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.50  % (13960)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (13980)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.51  % (13961)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (13960)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (13957)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f130,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    sK2 != k1_funct_1(sK4,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    sK2 != k1_funct_1(sK4,sK3) & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK2 != k1_funct_1(sK4,sK3) & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.52    inference(negated_conjecture,[],[f13])).
% 0.22/0.52  fof(f13,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    sK2 = k1_funct_1(sK4,sK3)),
% 0.22/0.52    inference(resolution,[],[f129,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    r2_hidden(sK3,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | sK2 = k1_funct_1(sK4,X0)) )),
% 0.22/0.52    inference(resolution,[],[f128,f111])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ( ! [X8,X7] : (~r2_hidden(X8,k1_tarski(X7)) | X7 = X8) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f110])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ( ! [X8,X7] : (X7 = X8 | X7 = X8 | ~r2_hidden(X8,k1_tarski(X7)) | X7 = X8) )),
% 0.22/0.52    inference(resolution,[],[f51,f95])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ( ! [X0] : (sP0(X0,X0,X0,k1_tarski(X0))) )),
% 0.22/0.52    inference(superposition,[],[f86,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sP0(X1,X0,X0,k2_tarski(X0,X1))) )),
% 0.22/0.52    inference(superposition,[],[f65,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 0.22/0.52    inference(equality_resolution,[],[f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.22/0.52    inference(nnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 0.22/0.52    inference(definition_folding,[],[f23,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.52    inference(rectify,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.22/0.52    inference(flattening,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.22/0.52    inference(nnf_transformation,[],[f24])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2)) | ~r2_hidden(X0,sK1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f127,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_funct_2(sK4,sK1,k1_tarski(sK2)) | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f126,f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X2] : (k1_xboole_0 != k1_tarski(X2)) )),
% 0.22/0.52    inference(superposition,[],[f69,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X0] : (k2_xboole_0(sK5(X0),X0) = X0) )),
% 0.22/0.52    inference(resolution,[],[f46,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(sK5(X0),X0)) )),
% 0.22/0.52    inference(resolution,[],[f47,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(sK5(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0] : m1_subset_1(sK5(X0),k1_zfmisc_1(X0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(sK5(X0),k1_zfmisc_1(X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : ? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.52    inference(unused_predicate_definition_removal,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(X1,k1_tarski(X0))) )),
% 0.22/0.52    inference(superposition,[],[f43,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = k1_tarski(sK2) | ~v1_funct_2(sK4,sK1,k1_tarski(sK2)) | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2))) )),
% 0.22/0.52    inference(resolution,[],[f125,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~v1_funct_2(sK4,X2,X0) | r2_hidden(k1_funct_1(sK4,X1),X0)) )),
% 0.22/0.52    inference(resolution,[],[f50,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    v1_funct_1(sK4)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (13960)------------------------------
% 0.22/0.52  % (13960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13960)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (13960)Memory used [KB]: 6268
% 0.22/0.52  % (13960)Time elapsed: 0.110 s
% 0.22/0.52  % (13960)------------------------------
% 0.22/0.52  % (13960)------------------------------
% 0.22/0.52  % (13952)Success in time 0.161 s
%------------------------------------------------------------------------------
