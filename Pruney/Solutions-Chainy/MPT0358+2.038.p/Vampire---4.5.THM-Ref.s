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
% DateTime   : Thu Dec  3 12:44:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 789 expanded)
%              Number of leaves         :   14 ( 184 expanded)
%              Depth                    :   24
%              Number of atoms          :  234 (2609 expanded)
%              Number of equality atoms :   74 (1000 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(resolution,[],[f245,f140])).

fof(f140,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f34,f139])).

fof(f139,plain,(
    k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f134,f108])).

fof(f108,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f59,f101])).

fof(f101,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f43,f34])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f59,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

% (9412)Refutation not found, incomplete strategy% (9412)------------------------------
% (9412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9412)Termination reason: Refutation not found, incomplete strategy

% (9412)Memory used [KB]: 10618
% (9412)Time elapsed: 0.133 s
% (9412)------------------------------
% (9412)------------------------------
fof(f35,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( sK1 != k1_subset_1(sK0)
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( sK1 = k1_subset_1(sK0)
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k1_subset_1(sK0)
        | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & ( sK1 = k1_subset_1(sK0)
        | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f134,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f75,f129])).

fof(f129,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f121,f34])).

fof(f121,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f119,f105])).

fof(f105,plain,(
    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f96,f101])).

fof(f96,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f42,f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f119,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f109,f43])).

fof(f109,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f50,f101])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f45,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f245,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f196,f234])).

fof(f234,plain,(
    sK0 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f224,f140])).

fof(f224,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | sK0 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f215,f147])).

fof(f147,plain,
    ( m1_subset_1(k4_xboole_0(sK0,k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f144,f139])).

fof(f144,plain,
    ( m1_subset_1(k4_xboole_0(sK0,k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f109,f139])).

fof(f215,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK0,k1_xboole_0),k1_zfmisc_1(sK0))
    | sK0 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f212,f55])).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f212,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k4_xboole_0(sK0,k1_xboole_0),k1_zfmisc_1(sK0))
    | sK0 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f177,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f177,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,k1_xboole_0),k1_zfmisc_1(sK0))
    | sK0 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f168,f63])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
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
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
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
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f168,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK0)
    | sK0 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f165])).

fof(f165,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK0) ),
    inference(superposition,[],[f83,f145])).

fof(f145,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f129,f139])).

fof(f83,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,X2)
      | X1 = X2
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f196,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f160,f55])).

fof(f160,plain,
    ( v1_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f154,f51])).

fof(f154,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f151,f142])).

fof(f142,plain,(
    k3_subset_1(sK0,k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f101,f139])).

fof(f151,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k3_subset_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f146,f63])).

fof(f146,plain,(
    ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f141])).

fof(f141,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f65,f139])).

fof(f65,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(inner_rewriting,[],[f58])).

fof(f58,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f36,f44])).

fof(f36,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:53:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (9405)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (9420)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (9422)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (9405)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (9401)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (9428)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (9401)Refutation not found, incomplete strategy% (9401)------------------------------
% 0.21/0.55  % (9401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9401)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9401)Memory used [KB]: 1663
% 0.21/0.55  % (9401)Time elapsed: 0.119 s
% 0.21/0.55  % (9401)------------------------------
% 0.21/0.55  % (9401)------------------------------
% 0.21/0.56  % (9403)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  % (9412)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.37/0.56  % SZS output start Proof for theBenchmark
% 1.37/0.56  fof(f256,plain,(
% 1.37/0.56    $false),
% 1.37/0.56    inference(resolution,[],[f245,f140])).
% 1.37/0.56  fof(f140,plain,(
% 1.37/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 1.37/0.56    inference(backward_demodulation,[],[f34,f139])).
% 1.37/0.56  fof(f139,plain,(
% 1.37/0.56    k1_xboole_0 = sK1),
% 1.37/0.56    inference(duplicate_literal_removal,[],[f136])).
% 1.37/0.56  fof(f136,plain,(
% 1.37/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.37/0.56    inference(resolution,[],[f134,f108])).
% 1.37/0.56  fof(f108,plain,(
% 1.37/0.56    r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 1.37/0.56    inference(backward_demodulation,[],[f59,f101])).
% 1.37/0.56  fof(f101,plain,(
% 1.37/0.56    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.37/0.56    inference(resolution,[],[f43,f34])).
% 1.37/0.56  fof(f43,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f17])).
% 1.37/0.56  fof(f17,plain,(
% 1.37/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.56    inference(ennf_transformation,[],[f9])).
% 1.37/0.56  fof(f9,axiom,(
% 1.37/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.37/0.56  fof(f59,plain,(
% 1.37/0.56    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | k1_xboole_0 = sK1),
% 1.37/0.56    inference(definition_unfolding,[],[f35,f44])).
% 1.37/0.56  fof(f44,plain,(
% 1.37/0.56    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f8])).
% 1.37/0.56  fof(f8,axiom,(
% 1.37/0.56    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.37/0.56  % (9412)Refutation not found, incomplete strategy% (9412)------------------------------
% 1.37/0.56  % (9412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (9412)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (9412)Memory used [KB]: 10618
% 1.37/0.56  % (9412)Time elapsed: 0.133 s
% 1.37/0.56  % (9412)------------------------------
% 1.37/0.56  % (9412)------------------------------
% 1.37/0.56  fof(f35,plain,(
% 1.37/0.56    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.37/0.56    inference(cnf_transformation,[],[f25])).
% 1.37/0.56  fof(f25,plain,(
% 1.37/0.56    (sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.37/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 1.37/0.56  fof(f24,plain,(
% 1.37/0.56    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.37/0.56    introduced(choice_axiom,[])).
% 1.37/0.56  fof(f23,plain,(
% 1.37/0.56    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.56    inference(flattening,[],[f22])).
% 1.37/0.56  fof(f22,plain,(
% 1.37/0.56    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.56    inference(nnf_transformation,[],[f15])).
% 1.37/0.56  fof(f15,plain,(
% 1.37/0.56    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.56    inference(ennf_transformation,[],[f14])).
% 1.37/0.56  fof(f14,negated_conjecture,(
% 1.37/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.37/0.56    inference(negated_conjecture,[],[f13])).
% 1.37/0.56  fof(f13,conjecture,(
% 1.37/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 1.37/0.56  fof(f134,plain,(
% 1.37/0.56    ~r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 1.37/0.56    inference(superposition,[],[f75,f129])).
% 1.37/0.56  fof(f129,plain,(
% 1.37/0.56    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.37/0.56    inference(resolution,[],[f121,f34])).
% 1.37/0.56  fof(f121,plain,(
% 1.37/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.37/0.56    inference(forward_demodulation,[],[f119,f105])).
% 1.37/0.56  fof(f105,plain,(
% 1.37/0.56    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 1.37/0.56    inference(backward_demodulation,[],[f96,f101])).
% 1.37/0.56  fof(f96,plain,(
% 1.37/0.56    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 1.37/0.56    inference(resolution,[],[f42,f34])).
% 1.37/0.56  fof(f42,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.37/0.56    inference(cnf_transformation,[],[f16])).
% 1.37/0.56  fof(f16,plain,(
% 1.37/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.56    inference(ennf_transformation,[],[f12])).
% 1.37/0.56  fof(f12,axiom,(
% 1.37/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.37/0.56  fof(f119,plain,(
% 1.37/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.37/0.56    inference(resolution,[],[f109,f43])).
% 1.37/0.56  fof(f109,plain,(
% 1.37/0.56    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.37/0.56    inference(superposition,[],[f50,f101])).
% 1.37/0.56  fof(f50,plain,(
% 1.37/0.56    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.56    inference(cnf_transformation,[],[f19])).
% 1.37/0.56  fof(f19,plain,(
% 1.37/0.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.56    inference(ennf_transformation,[],[f10])).
% 1.37/0.56  fof(f10,axiom,(
% 1.37/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.37/0.56  fof(f75,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.37/0.56    inference(resolution,[],[f45,f57])).
% 1.37/0.56  fof(f57,plain,(
% 1.37/0.56    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.37/0.56    inference(cnf_transformation,[],[f21])).
% 1.37/0.56  fof(f21,plain,(
% 1.37/0.56    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.37/0.56    inference(ennf_transformation,[],[f4])).
% 1.37/0.56  fof(f4,axiom,(
% 1.37/0.56    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.37/0.56  fof(f45,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f18])).
% 1.37/0.56  fof(f18,plain,(
% 1.37/0.56    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.37/0.56    inference(ennf_transformation,[],[f5])).
% 1.37/0.56  fof(f5,axiom,(
% 1.37/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.37/0.56  fof(f34,plain,(
% 1.37/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.37/0.56    inference(cnf_transformation,[],[f25])).
% 1.37/0.56  fof(f245,plain,(
% 1.37/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 1.37/0.56    inference(backward_demodulation,[],[f196,f234])).
% 1.37/0.56  fof(f234,plain,(
% 1.37/0.56    sK0 = k4_xboole_0(sK0,k1_xboole_0)),
% 1.37/0.56    inference(resolution,[],[f224,f140])).
% 1.37/0.56  fof(f224,plain,(
% 1.37/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | sK0 = k4_xboole_0(sK0,k1_xboole_0)),
% 1.37/0.56    inference(resolution,[],[f215,f147])).
% 1.37/0.56  fof(f147,plain,(
% 1.37/0.56    m1_subset_1(k4_xboole_0(sK0,k1_xboole_0),k1_zfmisc_1(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 1.37/0.56    inference(forward_demodulation,[],[f144,f139])).
% 1.37/0.56  fof(f144,plain,(
% 1.37/0.56    m1_subset_1(k4_xboole_0(sK0,k1_xboole_0),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.37/0.56    inference(backward_demodulation,[],[f109,f139])).
% 1.37/0.56  fof(f215,plain,(
% 1.37/0.56    ~m1_subset_1(k4_xboole_0(sK0,k1_xboole_0),k1_zfmisc_1(sK0)) | sK0 = k4_xboole_0(sK0,k1_xboole_0)),
% 1.37/0.56    inference(resolution,[],[f212,f55])).
% 1.37/0.56  fof(f55,plain,(
% 1.37/0.56    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.37/0.56    inference(cnf_transformation,[],[f11])).
% 1.37/0.56  fof(f11,axiom,(
% 1.37/0.56    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.37/0.56  fof(f212,plain,(
% 1.37/0.56    v1_xboole_0(k1_zfmisc_1(sK0)) | ~m1_subset_1(k4_xboole_0(sK0,k1_xboole_0),k1_zfmisc_1(sK0)) | sK0 = k4_xboole_0(sK0,k1_xboole_0)),
% 1.37/0.56    inference(resolution,[],[f177,f51])).
% 1.37/0.56  fof(f51,plain,(
% 1.37/0.56    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f33])).
% 1.37/0.56  fof(f33,plain,(
% 1.37/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.37/0.56    inference(nnf_transformation,[],[f20])).
% 1.37/0.56  fof(f20,plain,(
% 1.37/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.37/0.56    inference(ennf_transformation,[],[f7])).
% 1.37/0.56  fof(f7,axiom,(
% 1.37/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.37/0.56  fof(f177,plain,(
% 1.37/0.56    ~r2_hidden(k4_xboole_0(sK0,k1_xboole_0),k1_zfmisc_1(sK0)) | sK0 = k4_xboole_0(sK0,k1_xboole_0)),
% 1.37/0.56    inference(resolution,[],[f168,f63])).
% 1.37/0.56  fof(f63,plain,(
% 1.37/0.56    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.37/0.56    inference(equality_resolution,[],[f46])).
% 1.37/0.56  fof(f46,plain,(
% 1.37/0.56    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.37/0.56    inference(cnf_transformation,[],[f32])).
% 1.37/0.56  fof(f32,plain,(
% 1.37/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.37/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 1.37/0.56  fof(f31,plain,(
% 1.37/0.56    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.37/0.56    introduced(choice_axiom,[])).
% 1.37/0.56  fof(f30,plain,(
% 1.37/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.37/0.56    inference(rectify,[],[f29])).
% 1.37/0.56  fof(f29,plain,(
% 1.37/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.37/0.56    inference(nnf_transformation,[],[f6])).
% 1.37/0.56  fof(f6,axiom,(
% 1.37/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.37/0.56  fof(f168,plain,(
% 1.37/0.56    ~r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK0) | sK0 = k4_xboole_0(sK0,k1_xboole_0)),
% 1.37/0.56    inference(trivial_inequality_removal,[],[f165])).
% 1.37/0.56  fof(f165,plain,(
% 1.37/0.56    k1_xboole_0 != k1_xboole_0 | sK0 = k4_xboole_0(sK0,k1_xboole_0) | ~r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK0)),
% 1.37/0.56    inference(superposition,[],[f83,f145])).
% 1.37/0.56  fof(f145,plain,(
% 1.37/0.56    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))),
% 1.37/0.56    inference(backward_demodulation,[],[f129,f139])).
% 1.37/0.56  fof(f83,plain,(
% 1.37/0.56    ( ! [X2,X1] : (k1_xboole_0 != k4_xboole_0(X1,X2) | X1 = X2 | ~r1_tarski(X2,X1)) )),
% 1.37/0.56    inference(resolution,[],[f41,f37])).
% 1.37/0.56  fof(f37,plain,(
% 1.37/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.37/0.56    inference(cnf_transformation,[],[f26])).
% 1.37/0.56  fof(f26,plain,(
% 1.37/0.56    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.37/0.56    inference(nnf_transformation,[],[f2])).
% 1.37/0.56  fof(f2,axiom,(
% 1.37/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.37/0.56  fof(f41,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.37/0.56    inference(cnf_transformation,[],[f28])).
% 1.37/0.56  fof(f28,plain,(
% 1.37/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.56    inference(flattening,[],[f27])).
% 1.37/0.56  fof(f27,plain,(
% 1.37/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.56    inference(nnf_transformation,[],[f1])).
% 1.37/0.56  fof(f1,axiom,(
% 1.37/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.37/0.56  fof(f196,plain,(
% 1.37/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0)))),
% 1.37/0.56    inference(resolution,[],[f160,f55])).
% 1.37/0.56  fof(f160,plain,(
% 1.37/0.56    v1_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0)))),
% 1.37/0.56    inference(resolution,[],[f154,f51])).
% 1.37/0.56  fof(f154,plain,(
% 1.37/0.56    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0)))),
% 1.37/0.56    inference(backward_demodulation,[],[f151,f142])).
% 1.37/0.56  fof(f142,plain,(
% 1.37/0.56    k3_subset_1(sK0,k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.37/0.56    inference(backward_demodulation,[],[f101,f139])).
% 1.37/0.56  fof(f151,plain,(
% 1.37/0.56    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k3_subset_1(sK0,k1_xboole_0)))),
% 1.37/0.56    inference(resolution,[],[f146,f63])).
% 1.37/0.56  fof(f146,plain,(
% 1.37/0.56    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 1.37/0.56    inference(trivial_inequality_removal,[],[f141])).
% 1.37/0.56  fof(f141,plain,(
% 1.37/0.56    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 1.37/0.56    inference(backward_demodulation,[],[f65,f139])).
% 1.37/0.56  fof(f65,plain,(
% 1.37/0.56    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 1.37/0.56    inference(inner_rewriting,[],[f58])).
% 1.37/0.56  fof(f58,plain,(
% 1.37/0.56    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.37/0.56    inference(definition_unfolding,[],[f36,f44])).
% 1.37/0.56  fof(f36,plain,(
% 1.37/0.56    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.37/0.56    inference(cnf_transformation,[],[f25])).
% 1.37/0.56  % SZS output end Proof for theBenchmark
% 1.37/0.56  % (9405)------------------------------
% 1.37/0.56  % (9405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (9405)Termination reason: Refutation
% 1.37/0.56  
% 1.37/0.56  % (9405)Memory used [KB]: 1791
% 1.37/0.56  % (9405)Time elapsed: 0.127 s
% 1.37/0.56  % (9405)------------------------------
% 1.37/0.56  % (9405)------------------------------
% 1.37/0.56  % (9399)Success in time 0.2 s
%------------------------------------------------------------------------------
