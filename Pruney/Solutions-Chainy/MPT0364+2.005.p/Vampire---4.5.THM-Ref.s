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
% DateTime   : Thu Dec  3 12:45:11 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 146 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  233 ( 475 expanded)
%              Number of equality atoms :   35 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f814,plain,(
    $false ),
    inference(subsumption_resolution,[],[f813,f140])).

fof(f140,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f139,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f139,plain,
    ( ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK3))
    | ~ r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f137,f45])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ r1_tarski(sK2,sK3)
      | ~ r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) )
    & ( r1_tarski(sK2,sK3)
      | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f35,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK2,X2)
            | ~ r1_xboole_0(sK2,k3_subset_1(sK1,X2)) )
          & ( r1_tarski(sK2,X2)
            | r1_xboole_0(sK2,k3_subset_1(sK1,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK2,X2)
          | ~ r1_xboole_0(sK2,k3_subset_1(sK1,X2)) )
        & ( r1_tarski(sK2,X2)
          | r1_xboole_0(sK2,k3_subset_1(sK1,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
   => ( ( ~ r1_tarski(sK2,sK3)
        | ~ r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) )
      & ( r1_tarski(sK2,sK3)
        | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(f137,plain,
    ( ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK3))
    | ~ r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f47,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f47,plain,
    ( ~ r1_xboole_0(sK2,k3_subset_1(sK1,sK3))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f813,plain,(
    r1_tarski(sK2,sK3) ),
    inference(forward_demodulation,[],[f797,f214])).

fof(f214,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f77,f169])).

fof(f169,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f162,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f162,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f76,f77])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f77,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f51,f57])).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f797,plain,(
    r1_tarski(k4_xboole_0(sK2,k1_xboole_0),sK3) ),
    inference(superposition,[],[f177,f729])).

fof(f729,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f724,f202])).

fof(f202,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,k4_xboole_0(X6,X7))
      | k1_xboole_0 = k4_xboole_0(X6,X7) ) ),
    inference(superposition,[],[f80,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f57])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f724,plain,(
    r1_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(resolution,[],[f326,f171])).

fof(f171,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(resolution,[],[f142,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f142,plain,(
    r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f141,f73])).

fof(f141,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK1,sK3))
    | r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f138,f45])).

fof(f138,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK1,sK3))
    | r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f46,f62])).

fof(f46,plain,
    ( r1_xboole_0(sK2,k3_subset_1(sK1,sK3))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f326,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK1,X0)
      | r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f317,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f317,plain,(
    r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f115,f108])).

fof(f108,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f105,f48])).

fof(f48,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f105,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f58,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f65,f84])).

fof(f84,plain,(
    ! [X0] : sP0(X0,k1_zfmisc_1(X0)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f16,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | r1_tarski(X3,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f177,plain,(
    ! [X8,X7] : r1_tarski(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7) ),
    inference(superposition,[],[f78,f79])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f53,f57,f57])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (25069)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (25062)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (25060)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  % (25075)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (25063)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (25058)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.56  % (25070)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.56  % (25083)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (25079)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.56  % (25080)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.56  % (25067)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (25065)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (25088)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (25078)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (25072)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.57  % (25064)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.57  % (25071)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.57  % (25086)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.58  % (25057)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.58  % (25079)Refutation not found, incomplete strategy% (25079)------------------------------
% 0.20/0.58  % (25079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (25079)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (25079)Memory used [KB]: 10746
% 0.20/0.58  % (25079)Time elapsed: 0.148 s
% 0.20/0.58  % (25079)------------------------------
% 0.20/0.58  % (25079)------------------------------
% 0.20/0.59  % (25084)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.59  % (25059)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.60  % (25081)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.60  % (25073)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.88/0.61  % (25088)Refutation found. Thanks to Tanya!
% 1.88/0.61  % SZS status Theorem for theBenchmark
% 1.88/0.61  % SZS output start Proof for theBenchmark
% 1.88/0.61  fof(f814,plain,(
% 1.88/0.61    $false),
% 1.88/0.61    inference(subsumption_resolution,[],[f813,f140])).
% 1.88/0.61  fof(f140,plain,(
% 1.88/0.61    ~r1_tarski(sK2,sK3)),
% 1.88/0.61    inference(subsumption_resolution,[],[f139,f73])).
% 1.88/0.61  fof(f73,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f26])).
% 1.88/0.61  fof(f26,plain,(
% 1.88/0.61    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.88/0.61    inference(ennf_transformation,[],[f13])).
% 1.88/0.61  fof(f13,axiom,(
% 1.88/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.88/0.61  fof(f139,plain,(
% 1.88/0.61    ~r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) | ~r1_tarski(sK2,sK3)),
% 1.88/0.61    inference(subsumption_resolution,[],[f137,f45])).
% 1.88/0.61  fof(f45,plain,(
% 1.88/0.61    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 1.88/0.61    inference(cnf_transformation,[],[f36])).
% 1.88/0.61  fof(f36,plain,(
% 1.88/0.61    ((~r1_tarski(sK2,sK3) | ~r1_xboole_0(sK2,k3_subset_1(sK1,sK3))) & (r1_tarski(sK2,sK3) | r1_xboole_0(sK2,k3_subset_1(sK1,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 1.88/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f35,f34])).
% 1.88/0.61  fof(f34,plain,(
% 1.88/0.61    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK2,X2) | ~r1_xboole_0(sK2,k3_subset_1(sK1,X2))) & (r1_tarski(sK2,X2) | r1_xboole_0(sK2,k3_subset_1(sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f35,plain,(
% 1.88/0.61    ? [X2] : ((~r1_tarski(sK2,X2) | ~r1_xboole_0(sK2,k3_subset_1(sK1,X2))) & (r1_tarski(sK2,X2) | r1_xboole_0(sK2,k3_subset_1(sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK1))) => ((~r1_tarski(sK2,sK3) | ~r1_xboole_0(sK2,k3_subset_1(sK1,sK3))) & (r1_tarski(sK2,sK3) | r1_xboole_0(sK2,k3_subset_1(sK1,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(sK1)))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f33,plain,(
% 1.88/0.61    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.88/0.61    inference(flattening,[],[f32])).
% 1.88/0.61  fof(f32,plain,(
% 1.88/0.61    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.88/0.61    inference(nnf_transformation,[],[f23])).
% 1.88/0.61  fof(f23,plain,(
% 1.88/0.61    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.88/0.61    inference(ennf_transformation,[],[f21])).
% 1.88/0.61  fof(f21,negated_conjecture,(
% 1.88/0.61    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 1.88/0.61    inference(negated_conjecture,[],[f20])).
% 1.88/0.61  fof(f20,conjecture,(
% 1.88/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).
% 1.88/0.61  fof(f137,plain,(
% 1.88/0.61    ~r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) | ~r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 1.88/0.61    inference(superposition,[],[f47,f62])).
% 1.88/0.61  fof(f62,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f25])).
% 1.88/0.61  fof(f25,plain,(
% 1.88/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.88/0.61    inference(ennf_transformation,[],[f18])).
% 1.88/0.61  fof(f18,axiom,(
% 1.88/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.88/0.61  fof(f47,plain,(
% 1.88/0.61    ~r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) | ~r1_tarski(sK2,sK3)),
% 1.88/0.61    inference(cnf_transformation,[],[f36])).
% 1.88/0.61  fof(f813,plain,(
% 1.88/0.61    r1_tarski(sK2,sK3)),
% 1.88/0.61    inference(forward_demodulation,[],[f797,f214])).
% 1.88/0.61  fof(f214,plain,(
% 1.88/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.88/0.61    inference(backward_demodulation,[],[f77,f169])).
% 1.88/0.61  fof(f169,plain,(
% 1.88/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.88/0.61    inference(forward_demodulation,[],[f162,f49])).
% 1.88/0.61  fof(f49,plain,(
% 1.88/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f15])).
% 1.88/0.61  fof(f15,axiom,(
% 1.88/0.61    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.88/0.61  fof(f162,plain,(
% 1.88/0.61    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 1.88/0.61    inference(superposition,[],[f76,f77])).
% 1.88/0.61  fof(f76,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.88/0.61    inference(definition_unfolding,[],[f56,f57])).
% 1.88/0.61  fof(f57,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f9])).
% 1.88/0.61  fof(f9,axiom,(
% 1.88/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.88/0.61  fof(f56,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f5])).
% 1.88/0.61  fof(f5,axiom,(
% 1.88/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.88/0.61  fof(f77,plain,(
% 1.88/0.61    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.88/0.61    inference(definition_unfolding,[],[f51,f57])).
% 1.88/0.61  fof(f51,plain,(
% 1.88/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.88/0.61    inference(cnf_transformation,[],[f22])).
% 1.88/0.61  fof(f22,plain,(
% 1.88/0.61    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.88/0.61    inference(rectify,[],[f4])).
% 1.88/0.61  fof(f4,axiom,(
% 1.88/0.61    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.88/0.61  fof(f797,plain,(
% 1.88/0.61    r1_tarski(k4_xboole_0(sK2,k1_xboole_0),sK3)),
% 1.88/0.61    inference(superposition,[],[f177,f729])).
% 1.88/0.61  fof(f729,plain,(
% 1.88/0.61    k1_xboole_0 = k4_xboole_0(sK2,sK3)),
% 1.88/0.61    inference(resolution,[],[f724,f202])).
% 1.88/0.61  fof(f202,plain,(
% 1.88/0.61    ( ! [X6,X7] : (~r1_xboole_0(X6,k4_xboole_0(X6,X7)) | k1_xboole_0 = k4_xboole_0(X6,X7)) )),
% 1.88/0.61    inference(superposition,[],[f80,f82])).
% 1.88/0.61  fof(f82,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.88/0.61    inference(definition_unfolding,[],[f63,f57])).
% 1.88/0.61  fof(f63,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f38])).
% 1.88/0.61  fof(f38,plain,(
% 1.88/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.88/0.61    inference(nnf_transformation,[],[f3])).
% 1.88/0.61  fof(f3,axiom,(
% 1.88/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.88/0.61  fof(f80,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.88/0.61    inference(definition_unfolding,[],[f55,f57])).
% 1.88/0.61  fof(f55,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f8])).
% 1.88/0.61  fof(f8,axiom,(
% 1.88/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.88/0.61  fof(f724,plain,(
% 1.88/0.61    r1_xboole_0(sK2,k4_xboole_0(sK2,sK3))),
% 1.88/0.61    inference(resolution,[],[f326,f171])).
% 1.88/0.61  fof(f171,plain,(
% 1.88/0.61    r1_xboole_0(sK1,k4_xboole_0(sK2,sK3))),
% 1.88/0.61    inference(resolution,[],[f142,f74])).
% 1.88/0.61  fof(f74,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X1,k4_xboole_0(X0,X2))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f27])).
% 1.88/0.61  fof(f27,plain,(
% 1.88/0.61    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 1.88/0.61    inference(ennf_transformation,[],[f12])).
% 1.88/0.61  fof(f12,axiom,(
% 1.88/0.61    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 1.88/0.61  fof(f142,plain,(
% 1.88/0.61    r1_xboole_0(sK2,k4_xboole_0(sK1,sK3))),
% 1.88/0.61    inference(subsumption_resolution,[],[f141,f73])).
% 1.88/0.61  fof(f141,plain,(
% 1.88/0.61    r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) | r1_tarski(sK2,sK3)),
% 1.88/0.61    inference(subsumption_resolution,[],[f138,f45])).
% 1.88/0.61  fof(f138,plain,(
% 1.88/0.61    r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) | r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 1.88/0.61    inference(superposition,[],[f46,f62])).
% 1.88/0.61  fof(f46,plain,(
% 1.88/0.61    r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) | r1_tarski(sK2,sK3)),
% 1.88/0.61    inference(cnf_transformation,[],[f36])).
% 1.88/0.61  fof(f326,plain,(
% 1.88/0.61    ( ! [X0] : (~r1_xboole_0(sK1,X0) | r1_xboole_0(sK2,X0)) )),
% 1.88/0.61    inference(resolution,[],[f317,f75])).
% 1.88/0.61  fof(f75,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f29])).
% 1.88/0.61  fof(f29,plain,(
% 1.88/0.61    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.88/0.61    inference(flattening,[],[f28])).
% 1.88/0.61  fof(f28,plain,(
% 1.88/0.61    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.88/0.61    inference(ennf_transformation,[],[f11])).
% 1.88/0.61  fof(f11,axiom,(
% 1.88/0.61    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.88/0.61  fof(f317,plain,(
% 1.88/0.61    r1_tarski(sK2,sK1)),
% 1.88/0.61    inference(resolution,[],[f115,f108])).
% 1.88/0.61  fof(f108,plain,(
% 1.88/0.61    r2_hidden(sK2,k1_zfmisc_1(sK1))),
% 1.88/0.61    inference(subsumption_resolution,[],[f105,f48])).
% 1.88/0.61  fof(f48,plain,(
% 1.88/0.61    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f19])).
% 1.88/0.61  fof(f19,axiom,(
% 1.88/0.61    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.88/0.61  fof(f105,plain,(
% 1.88/0.61    r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1))),
% 1.88/0.61    inference(resolution,[],[f58,f44])).
% 1.88/0.61  fof(f44,plain,(
% 1.88/0.61    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 1.88/0.61    inference(cnf_transformation,[],[f36])).
% 1.88/0.61  fof(f58,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f37])).
% 1.88/0.61  fof(f37,plain,(
% 1.88/0.61    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.88/0.61    inference(nnf_transformation,[],[f24])).
% 1.88/0.61  fof(f24,plain,(
% 1.88/0.61    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.88/0.61    inference(ennf_transformation,[],[f17])).
% 1.88/0.61  fof(f17,axiom,(
% 1.88/0.61    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.88/0.61  fof(f115,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.88/0.61    inference(resolution,[],[f65,f84])).
% 1.88/0.61  fof(f84,plain,(
% 1.88/0.61    ( ! [X0] : (sP0(X0,k1_zfmisc_1(X0))) )),
% 1.88/0.61    inference(equality_resolution,[],[f69])).
% 1.88/0.61  fof(f69,plain,(
% 1.88/0.61    ( ! [X0,X1] : (sP0(X0,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.88/0.61    inference(cnf_transformation,[],[f43])).
% 1.88/0.61  fof(f43,plain,(
% 1.88/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_zfmisc_1(X0) != X1))),
% 1.88/0.61    inference(nnf_transformation,[],[f31])).
% 1.88/0.61  fof(f31,plain,(
% 1.88/0.61    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> sP0(X0,X1))),
% 1.88/0.61    inference(definition_folding,[],[f16,f30])).
% 1.88/0.61  fof(f30,plain,(
% 1.88/0.61    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.88/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.88/0.61  fof(f16,axiom,(
% 1.88/0.61    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.88/0.61  fof(f65,plain,(
% 1.88/0.61    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r2_hidden(X3,X1) | r1_tarski(X3,X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f42])).
% 1.88/0.61  fof(f42,plain,(
% 1.88/0.61    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 1.88/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 1.88/0.61  fof(f41,plain,(
% 1.88/0.61    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f40,plain,(
% 1.88/0.61    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 1.88/0.61    inference(rectify,[],[f39])).
% 1.88/0.61  fof(f39,plain,(
% 1.88/0.61    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 1.88/0.61    inference(nnf_transformation,[],[f30])).
% 1.88/0.61  fof(f177,plain,(
% 1.88/0.61    ( ! [X8,X7] : (r1_tarski(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7)) )),
% 1.88/0.61    inference(superposition,[],[f78,f79])).
% 1.88/0.61  fof(f79,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.88/0.61    inference(definition_unfolding,[],[f53,f57,f57])).
% 1.88/0.61  fof(f53,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f1])).
% 1.88/0.61  fof(f1,axiom,(
% 1.88/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.88/0.61  fof(f78,plain,(
% 1.88/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.88/0.61    inference(definition_unfolding,[],[f52,f57])).
% 1.88/0.61  fof(f52,plain,(
% 1.88/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f7])).
% 1.88/0.61  fof(f7,axiom,(
% 1.88/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.88/0.61  % SZS output end Proof for theBenchmark
% 1.88/0.61  % (25088)------------------------------
% 1.88/0.61  % (25088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (25088)Termination reason: Refutation
% 1.88/0.61  
% 1.88/0.61  % (25088)Memory used [KB]: 2174
% 1.88/0.61  % (25088)Time elapsed: 0.178 s
% 1.88/0.61  % (25088)------------------------------
% 1.88/0.61  % (25088)------------------------------
% 1.88/0.61  % (25054)Success in time 0.253 s
%------------------------------------------------------------------------------
