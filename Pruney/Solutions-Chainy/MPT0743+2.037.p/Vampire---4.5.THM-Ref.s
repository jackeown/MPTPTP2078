%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 295 expanded)
%              Number of leaves         :   12 (  68 expanded)
%              Depth                    :   28
%              Number of atoms          :  322 (1290 expanded)
%              Number of equality atoms :   40 (  94 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(resolution,[],[f302,f34])).

fof(f34,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f302,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f301,f53])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f301,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f300])).

fof(f300,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ r1_tarski(sK0,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f299,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f299,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ v3_ordinal1(sK0)
    | ~ r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f293,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f293,plain,
    ( r2_hidden(sK0,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(resolution,[],[f270,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(k1_ordinal1(X0),X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(resolution,[],[f38,f56])).

fof(f56,plain,(
    ! [X0] : ~ r1_tarski(k1_ordinal1(X0),X0) ),
    inference(resolution,[],[f47,f46])).

fof(f46,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f270,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK0)
    | r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f241,f239])).

fof(f239,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f238,f34])).

fof(f238,plain,
    ( ~ v3_ordinal1(sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f237,f35])).

fof(f35,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f237,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f221,f199])).

fof(f199,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,
    ( sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f195,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f195,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f181,f38])).

fof(f181,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f170,f45])).

fof(f170,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ v3_ordinal1(sK1)
    | ~ r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ v3_ordinal1(sK1)
    | ~ r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f157,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f48,f47])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f157,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ v3_ordinal1(sK1)
    | ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f149,f47])).

fof(f149,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f65,f36])).

fof(f36,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X2,X1] :
      ( ~ r1_ordinal1(k1_ordinal1(X1),X2)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(k1_ordinal1(X1))
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f38,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_ordinal1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f43,f47])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f221,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,
    ( sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f219,f38])).

fof(f219,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,
    ( ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | ~ r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f215,f45])).

fof(f215,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | ~ r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,
    ( sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ r1_tarski(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f173,f91])).

fof(f173,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f107,f37])).

fof(f37,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f107,plain,(
    ! [X8,X7] :
      ( r1_ordinal1(k1_ordinal1(X8),X7)
      | ~ r1_tarski(X8,X7)
      | X7 = X8
      | ~ v3_ordinal1(X7)
      | ~ v3_ordinal1(k1_ordinal1(X8)) ) ),
    inference(resolution,[],[f85,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | X0 = X1
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f42,f47])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f241,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK0)
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f36,f239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:46:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.44  % (23607)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.44  % (23607)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f305,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(resolution,[],[f302,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    v3_ordinal1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.47    inference(flattening,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f11])).
% 0.20/0.47  fof(f11,conjecture,(
% 0.20/0.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.20/0.47  fof(f302,plain,(
% 0.20/0.47    ~v3_ordinal1(sK0)),
% 0.20/0.47    inference(resolution,[],[f301,f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.47    inference(flattening,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.47  fof(f301,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK0) | ~v3_ordinal1(sK0)),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f300])).
% 0.20/0.47  fof(f300,plain,(
% 0.20/0.47    ~v3_ordinal1(sK0) | ~r1_tarski(sK0,sK0) | ~v3_ordinal1(sK0)),
% 0.20/0.47    inference(resolution,[],[f299,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.20/0.47  fof(f299,plain,(
% 0.20/0.47    ~v3_ordinal1(k1_ordinal1(sK0)) | ~v3_ordinal1(sK0) | ~r1_tarski(sK0,sK0)),
% 0.20/0.47    inference(resolution,[],[f293,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.47  fof(f293,plain,(
% 0.20/0.47    r2_hidden(sK0,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(k1_ordinal1(sK0))),
% 0.20/0.47    inference(resolution,[],[f270,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_ordinal1(k1_ordinal1(X0),X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(k1_ordinal1(X0))) )),
% 0.20/0.47    inference(resolution,[],[f38,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k1_ordinal1(X0),X0)) )),
% 0.20/0.47    inference(resolution,[],[f47,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.47  fof(f270,plain,(
% 0.20/0.47    r1_ordinal1(k1_ordinal1(sK0),sK0) | r2_hidden(sK0,sK0)),
% 0.20/0.47    inference(forward_demodulation,[],[f241,f239])).
% 0.20/0.47  fof(f239,plain,(
% 0.20/0.47    sK0 = sK1),
% 0.20/0.47    inference(resolution,[],[f238,f34])).
% 0.20/0.47  fof(f238,plain,(
% 0.20/0.47    ~v3_ordinal1(sK0) | sK0 = sK1),
% 0.20/0.47    inference(resolution,[],[f237,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    v3_ordinal1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | sK0 = sK1),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f230])).
% 0.20/0.47  fof(f230,plain,(
% 0.20/0.47    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK0 = sK1),
% 0.20/0.47    inference(resolution,[],[f221,f199])).
% 0.20/0.47  fof(f199,plain,(
% 0.20/0.47    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK0 = sK1),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f196])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.20/0.47    inference(resolution,[],[f195,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.47    inference(flattening,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    ~r1_ordinal1(sK1,sK0) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f194])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    ~v3_ordinal1(sK1) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.20/0.47    inference(resolution,[],[f181,f38])).
% 0.20/0.47  fof(f181,plain,(
% 0.20/0.47    ~r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1) | sK0 = sK1 | ~v3_ordinal1(sK0)),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f180])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    ~v3_ordinal1(sK1) | ~r1_tarski(sK1,sK0) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK0)),
% 0.20/0.47    inference(resolution,[],[f170,f45])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    ~v3_ordinal1(k1_ordinal1(sK0)) | ~v3_ordinal1(sK1) | ~r1_tarski(sK1,sK0) | sK0 = sK1 | ~v3_ordinal1(sK0)),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f164])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    ~v3_ordinal1(k1_ordinal1(sK0)) | ~v3_ordinal1(sK1) | ~r1_tarski(sK1,sK0) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | ~r1_tarski(sK1,sK0)),
% 0.20/0.47    inference(resolution,[],[f157,f91])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(resolution,[],[f48,f47])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    ~r2_hidden(sK1,sK0) | ~v3_ordinal1(k1_ordinal1(sK0)) | ~v3_ordinal1(sK1) | ~r1_tarski(sK1,sK0)),
% 0.20/0.47    inference(resolution,[],[f149,f47])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    r2_hidden(sK0,sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.20/0.47    inference(resolution,[],[f65,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X2,X1] : (~r1_ordinal1(k1_ordinal1(X1),X2) | ~v3_ordinal1(X2) | ~v3_ordinal1(k1_ordinal1(X1)) | ~r2_hidden(X2,X1)) )),
% 0.20/0.47    inference(resolution,[],[f38,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(k1_ordinal1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(resolution,[],[f43,f47])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.47    inference(flattening,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.20/0.47  fof(f221,plain,(
% 0.20/0.47    ~r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | sK0 = sK1),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f220])).
% 0.20/0.47  fof(f220,plain,(
% 0.20/0.47    sK0 = sK1 | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.20/0.47    inference(resolution,[],[f219,f38])).
% 0.20/0.47  fof(f219,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f218])).
% 0.20/0.47  fof(f218,plain,(
% 0.20/0.47    ~v3_ordinal1(sK1) | sK0 = sK1 | ~r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK0)),
% 0.20/0.47    inference(resolution,[],[f215,f45])).
% 0.20/0.47  fof(f215,plain,(
% 0.20/0.47    ~v3_ordinal1(k1_ordinal1(sK0)) | ~v3_ordinal1(sK1) | sK0 = sK1 | ~r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f208])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    sK0 = sK1 | ~v3_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | ~r1_tarski(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(resolution,[],[f173,f91])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    ~r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | ~r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(resolution,[],[f107,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ( ! [X8,X7] : (r1_ordinal1(k1_ordinal1(X8),X7) | ~r1_tarski(X8,X7) | X7 = X8 | ~v3_ordinal1(X7) | ~v3_ordinal1(k1_ordinal1(X8))) )),
% 0.20/0.47    inference(resolution,[],[f85,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | X0 = X1 | ~r1_tarski(X1,X0)) )),
% 0.20/0.47    inference(resolution,[],[f42,f47])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f241,plain,(
% 0.20/0.47    r1_ordinal1(k1_ordinal1(sK0),sK0) | r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(backward_demodulation,[],[f36,f239])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (23607)------------------------------
% 0.20/0.47  % (23607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (23607)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (23607)Memory used [KB]: 1791
% 0.20/0.47  % (23607)Time elapsed: 0.074 s
% 0.20/0.47  % (23607)------------------------------
% 0.20/0.47  % (23607)------------------------------
% 0.20/0.47  % (23601)Success in time 0.124 s
%------------------------------------------------------------------------------
