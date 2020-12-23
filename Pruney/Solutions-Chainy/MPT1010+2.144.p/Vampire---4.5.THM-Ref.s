%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:11 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 200 expanded)
%              Number of leaves         :   17 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  288 ( 646 expanded)
%              Number of equality atoms :  101 ( 251 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f50,f51,f305])).

fof(f305,plain,(
    ! [X0] :
      ( sK3 = k1_funct_1(sK5,X0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f304,f106])).

fof(f106,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f57,f95])).

fof(f95,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f94])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f72,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

% (17692)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (17680)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f304,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK5,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f303,f97])).

fof(f97,plain,(
    v1_funct_2(sK5,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f48,f95])).

fof(f48,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK3 != k1_funct_1(sK5,sK4)
    & r2_hidden(sK4,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f17,f25])).

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

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f303,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ v1_funct_2(sK5,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
      | r2_hidden(k1_funct_1(sK5,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ) ),
    inference(subsumption_resolution,[],[f302,f155])).

fof(f155,plain,(
    ! [X0] : k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(subsumption_resolution,[],[f152,f105])).

fof(f105,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f95])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f152,plain,(
    ! [X0] :
      ( k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(superposition,[],[f103,f127])).

fof(f127,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f120,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(k4_xboole_0(X0,X1)),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f108,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f120,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(k4_xboole_0(X0,X1)),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f109,f53])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f61,f95])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f302,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
      | ~ v1_funct_2(sK5,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
      | r2_hidden(k1_funct_1(sK5,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ) ),
    inference(resolution,[],[f286,f96])).

fof(f96,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f49,f95])).

fof(f49,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f286,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK5,X2,X0)
      | r2_hidden(k1_funct_1(sK5,X1),X0) ) ),
    inference(resolution,[],[f71,f47])).

fof(f47,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f51,plain,(
    sK3 != k1_funct_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (17665)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (17678)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (17663)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (17670)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (17664)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (17673)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (17686)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (17667)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (17684)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (17679)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (17664)Refutation not found, incomplete strategy% (17664)------------------------------
% 0.20/0.53  % (17664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (17664)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (17664)Memory used [KB]: 1791
% 0.20/0.53  % (17664)Time elapsed: 0.101 s
% 0.20/0.53  % (17664)------------------------------
% 0.20/0.53  % (17664)------------------------------
% 1.31/0.53  % (17676)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.31/0.53  % (17687)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.31/0.53  % (17666)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.31/0.53  % (17671)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.31/0.54  % (17675)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.31/0.54  % (17668)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.31/0.54  % (17669)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.54  % (17685)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.31/0.54  % (17674)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.31/0.54  % (17686)Refutation found. Thanks to Tanya!
% 1.31/0.54  % SZS status Theorem for theBenchmark
% 1.31/0.54  % SZS output start Proof for theBenchmark
% 1.31/0.54  fof(f307,plain,(
% 1.31/0.54    $false),
% 1.31/0.54    inference(unit_resulting_resolution,[],[f50,f51,f305])).
% 1.31/0.54  fof(f305,plain,(
% 1.31/0.54    ( ! [X0] : (sK3 = k1_funct_1(sK5,X0) | ~r2_hidden(X0,sK2)) )),
% 1.31/0.54    inference(resolution,[],[f304,f106])).
% 1.31/0.54  fof(f106,plain,(
% 1.31/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.31/0.54    inference(equality_resolution,[],[f101])).
% 1.31/0.54  fof(f101,plain,(
% 1.31/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.31/0.54    inference(definition_unfolding,[],[f57,f95])).
% 1.31/0.54  fof(f95,plain,(
% 1.31/0.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f52,f94])).
% 1.31/0.54  fof(f94,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f56,f93])).
% 1.31/0.54  fof(f93,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f63,f92])).
% 1.31/0.54  fof(f92,plain,(
% 1.31/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f70,f91])).
% 1.31/0.54  fof(f91,plain,(
% 1.31/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f72,f90])).
% 1.31/0.54  fof(f90,plain,(
% 1.31/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f73,f74])).
% 1.31/0.54  fof(f74,plain,(
% 1.31/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f9])).
% 1.31/0.54  fof(f9,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.31/0.54  fof(f73,plain,(
% 1.31/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f8])).
% 1.31/0.54  fof(f8,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.31/0.54  fof(f72,plain,(
% 1.31/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f7])).
% 1.31/0.54  fof(f7,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.31/0.54  fof(f70,plain,(
% 1.31/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f6])).
% 1.31/0.54  fof(f6,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.31/0.54  fof(f63,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f5])).
% 1.31/0.54  fof(f5,axiom,(
% 1.31/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.31/0.54  fof(f56,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f4])).
% 1.31/0.54  fof(f4,axiom,(
% 1.31/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.31/0.54  fof(f52,plain,(
% 1.31/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f3])).
% 1.31/0.54  fof(f3,axiom,(
% 1.31/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.31/0.54  fof(f57,plain,(
% 1.31/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.31/0.54    inference(cnf_transformation,[],[f32])).
% 1.31/0.54  % (17692)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.31/0.54  % (17680)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.31/0.54  fof(f32,plain,(
% 1.31/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f31])).
% 1.31/0.54  fof(f31,plain,(
% 1.31/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1))))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f30,plain,(
% 1.31/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.31/0.54    inference(rectify,[],[f29])).
% 1.31/0.54  fof(f29,plain,(
% 1.31/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.31/0.54    inference(nnf_transformation,[],[f2])).
% 1.31/0.54  fof(f2,axiom,(
% 1.31/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.31/0.54  fof(f304,plain,(
% 1.31/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK5,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(X0,sK2)) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f303,f97])).
% 1.31/0.54  fof(f97,plain,(
% 1.31/0.54    v1_funct_2(sK5,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),
% 1.31/0.54    inference(definition_unfolding,[],[f48,f95])).
% 1.31/0.54  fof(f48,plain,(
% 1.31/0.54    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 1.31/0.54    inference(cnf_transformation,[],[f26])).
% 1.31/0.54  fof(f26,plain,(
% 1.31/0.54    sK3 != k1_funct_1(sK5,sK4) & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f17,f25])).
% 1.31/0.54  fof(f25,plain,(
% 1.31/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK3 != k1_funct_1(sK5,sK4) & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f17,plain,(
% 1.31/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.31/0.54    inference(flattening,[],[f16])).
% 1.31/0.54  fof(f16,plain,(
% 1.31/0.54    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.31/0.54    inference(ennf_transformation,[],[f15])).
% 1.31/0.54  fof(f15,negated_conjecture,(
% 1.31/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.31/0.54    inference(negated_conjecture,[],[f14])).
% 1.31/0.54  fof(f14,conjecture,(
% 1.31/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 1.31/0.54  fof(f303,plain,(
% 1.31/0.54    ( ! [X0] : (~r2_hidden(X0,sK2) | ~v1_funct_2(sK5,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | r2_hidden(k1_funct_1(sK5,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f302,f155])).
% 1.31/0.54  fof(f155,plain,(
% 1.31/0.54    ( ! [X0] : (k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f152,f105])).
% 1.31/0.54  fof(f105,plain,(
% 1.31/0.54    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 1.31/0.54    inference(equality_resolution,[],[f104])).
% 1.31/0.54  fof(f104,plain,(
% 1.31/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 1.31/0.54    inference(equality_resolution,[],[f100])).
% 1.31/0.54  fof(f100,plain,(
% 1.31/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.31/0.54    inference(definition_unfolding,[],[f58,f95])).
% 1.31/0.54  fof(f58,plain,(
% 1.31/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.31/0.54    inference(cnf_transformation,[],[f32])).
% 1.31/0.54  fof(f152,plain,(
% 1.31/0.54    ( ! [X0] : (k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 1.31/0.54    inference(superposition,[],[f103,f127])).
% 1.31/0.54  fof(f127,plain,(
% 1.31/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.31/0.54    inference(duplicate_literal_removal,[],[f124])).
% 1.31/0.54  fof(f124,plain,(
% 1.31/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.31/0.54    inference(resolution,[],[f120,f119])).
% 1.31/0.54  fof(f119,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r2_hidden(sK6(k4_xboole_0(X0,X1)),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.31/0.54    inference(resolution,[],[f108,f53])).
% 1.31/0.54  fof(f53,plain,(
% 1.31/0.54    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 1.31/0.54    inference(cnf_transformation,[],[f28])).
% 1.31/0.54  fof(f28,plain,(
% 1.31/0.54    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f27])).
% 1.31/0.54  fof(f27,plain,(
% 1.31/0.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f18,plain,(
% 1.31/0.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.31/0.54    inference(ennf_transformation,[],[f12])).
% 1.31/0.55  fof(f12,axiom,(
% 1.31/0.55    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.31/0.55  fof(f108,plain,(
% 1.31/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.31/0.55    inference(equality_resolution,[],[f65])).
% 1.31/0.55  fof(f65,plain,(
% 1.31/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.31/0.55    inference(cnf_transformation,[],[f38])).
% 1.31/0.55  fof(f38,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((~r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.31/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f36,f37])).
% 1.31/0.55  fof(f37,plain,(
% 1.31/0.55    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((~r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 1.31/0.55    introduced(choice_axiom,[])).
% 1.31/0.55  fof(f36,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.31/0.55    inference(rectify,[],[f35])).
% 1.31/0.55  fof(f35,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.31/0.55    inference(flattening,[],[f34])).
% 1.31/0.55  fof(f34,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.31/0.55    inference(nnf_transformation,[],[f1])).
% 1.31/0.55  fof(f1,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.31/0.55  fof(f120,plain,(
% 1.31/0.55    ( ! [X0,X1] : (r2_hidden(sK6(k4_xboole_0(X0,X1)),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.31/0.55    inference(resolution,[],[f109,f53])).
% 1.31/0.55  fof(f109,plain,(
% 1.31/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.31/0.55    inference(equality_resolution,[],[f64])).
% 1.31/0.55  fof(f64,plain,(
% 1.31/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.31/0.55    inference(cnf_transformation,[],[f38])).
% 1.31/0.55  fof(f103,plain,(
% 1.31/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.31/0.55    inference(definition_unfolding,[],[f61,f95])).
% 1.31/0.55  fof(f61,plain,(
% 1.31/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.31/0.55    inference(cnf_transformation,[],[f33])).
% 1.31/0.55  fof(f33,plain,(
% 1.31/0.55    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.31/0.55    inference(nnf_transformation,[],[f10])).
% 1.31/0.55  fof(f10,axiom,(
% 1.31/0.55    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.31/0.55  fof(f302,plain,(
% 1.31/0.55    ( ! [X0] : (~r2_hidden(X0,sK2) | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~v1_funct_2(sK5,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | r2_hidden(k1_funct_1(sK5,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) )),
% 1.31/0.55    inference(resolution,[],[f286,f96])).
% 1.31/0.55  fof(f96,plain,(
% 1.31/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))),
% 1.31/0.55    inference(definition_unfolding,[],[f49,f95])).
% 1.31/0.55  fof(f49,plain,(
% 1.31/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 1.31/0.55    inference(cnf_transformation,[],[f26])).
% 1.31/0.55  fof(f286,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~v1_funct_2(sK5,X2,X0) | r2_hidden(k1_funct_1(sK5,X1),X0)) )),
% 1.31/0.55    inference(resolution,[],[f71,f47])).
% 1.31/0.55  fof(f47,plain,(
% 1.31/0.55    v1_funct_1(sK5)),
% 1.31/0.55    inference(cnf_transformation,[],[f26])).
% 1.31/0.55  fof(f71,plain,(
% 1.31/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f20])).
% 1.31/0.55  fof(f20,plain,(
% 1.31/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.31/0.55    inference(flattening,[],[f19])).
% 1.31/0.55  fof(f19,plain,(
% 1.31/0.55    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.31/0.55    inference(ennf_transformation,[],[f13])).
% 1.31/0.55  fof(f13,axiom,(
% 1.31/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 1.31/0.55  fof(f51,plain,(
% 1.31/0.55    sK3 != k1_funct_1(sK5,sK4)),
% 1.31/0.55    inference(cnf_transformation,[],[f26])).
% 1.31/0.55  fof(f50,plain,(
% 1.31/0.55    r2_hidden(sK4,sK2)),
% 1.31/0.55    inference(cnf_transformation,[],[f26])).
% 1.31/0.55  % SZS output end Proof for theBenchmark
% 1.31/0.55  % (17686)------------------------------
% 1.31/0.55  % (17686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (17686)Termination reason: Refutation
% 1.31/0.55  
% 1.31/0.55  % (17686)Memory used [KB]: 6524
% 1.31/0.55  % (17686)Time elapsed: 0.094 s
% 1.31/0.55  % (17686)------------------------------
% 1.31/0.55  % (17686)------------------------------
% 1.31/0.55  % (17693)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.31/0.55  % (17679)Refutation not found, incomplete strategy% (17679)------------------------------
% 1.31/0.55  % (17679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (17679)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (17679)Memory used [KB]: 10746
% 1.31/0.55  % (17679)Time elapsed: 0.138 s
% 1.31/0.55  % (17679)------------------------------
% 1.31/0.55  % (17679)------------------------------
% 1.31/0.55  % (17681)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.31/0.55  % (17659)Success in time 0.187 s
%------------------------------------------------------------------------------
