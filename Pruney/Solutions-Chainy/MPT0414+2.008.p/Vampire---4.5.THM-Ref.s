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
% DateTime   : Thu Dec  3 12:46:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 954 expanded)
%              Number of leaves         :   14 ( 249 expanded)
%              Depth                    :   28
%              Number of atoms          :  313 (4739 expanded)
%              Number of equality atoms :   38 ( 510 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f400,plain,(
    $false ),
    inference(subsumption_resolution,[],[f399,f332])).

fof(f332,plain,(
    k1_xboole_0 != sK2 ),
    inference(backward_demodulation,[],[f44,f322])).

fof(f322,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f320,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f320,plain,(
    v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f319,f126])).

fof(f126,plain,(
    r1_tarski(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,
    ( r1_tarski(sK2,sK1)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f121,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f121,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK2,X1),sK1)
      | r1_tarski(sK2,X1) ) ),
    inference(resolution,[],[f118,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f117,f104])).

fof(f104,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f101,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,(
    r1_tarski(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f96,f84])).

fof(f84,plain,(
    r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f79,f70])).

fof(f70,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f54,f53])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f74,f60])).

fof(f60,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK6(X0,X1),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r1_tarski(sK6(X0,X1),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK6(X0,X1),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( r1_tarski(sK6(X0,X1),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f74,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r1_tarski(sK1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f73,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f64,f61])).

fof(f61,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f49,f40])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( sK1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( sK1 != X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( sK1 != sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK1)
              | ~ r2_hidden(X3,sK2) )
            & ( r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f96,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(sK0))
      | r1_tarski(sK2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f77,f60])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r1_tarski(sK2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f76,f46])).

fof(f76,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r1_tarski(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f65,f61])).

fof(f65,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f49,f41])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f43,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f43,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f319,plain,
    ( v1_xboole_0(sK1)
    | ~ r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f318,f60])).

fof(f318,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f317,f48])).

fof(f317,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f314,f44])).

fof(f314,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | sK1 = sK2 ),
    inference(resolution,[],[f312,f190])).

fof(f190,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK4(X4,sK2),sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X4))
      | sK2 = X4 ) ),
    inference(resolution,[],[f51,f88])).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f87,f86])).

fof(f86,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f84,f52])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f42,f48])).

fof(f42,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f312,plain,
    ( r2_hidden(sK4(sK1,sK2),sK1)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f310,f44])).

fof(f310,plain,
    ( r2_hidden(sK4(sK1,sK2),sK1)
    | sK1 = sK2
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f286,f126])).

fof(f286,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f269,f60])).

fof(f269,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k1_zfmisc_1(X5))
      | v1_xboole_0(X5)
      | r2_hidden(sK4(X5,X6),X5)
      | X5 = X6 ) ),
    inference(resolution,[],[f134,f48])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_xboole_0(X0)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(resolution,[],[f50,f49])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f399,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f324,f45])).

fof(f324,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f120,f321])).

fof(f321,plain,(
    ! [X0] : ~ r2_hidden(X0,sK1) ),
    inference(resolution,[],[f320,f46])).

fof(f120,plain,
    ( r2_hidden(sK3(sK2),sK1)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f118,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:26:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (16362)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.49  % (16354)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (16354)Refutation not found, incomplete strategy% (16354)------------------------------
% 0.21/0.51  % (16354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16354)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16354)Memory used [KB]: 10746
% 0.21/0.51  % (16354)Time elapsed: 0.073 s
% 0.21/0.51  % (16354)------------------------------
% 0.21/0.51  % (16354)------------------------------
% 0.21/0.51  % (16347)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (16350)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (16349)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (16346)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (16351)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (16360)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (16353)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (16372)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (16356)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (16368)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (16348)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (16374)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (16348)Refutation not found, incomplete strategy% (16348)------------------------------
% 0.21/0.54  % (16348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16348)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16348)Memory used [KB]: 10746
% 0.21/0.54  % (16348)Time elapsed: 0.129 s
% 0.21/0.54  % (16348)------------------------------
% 0.21/0.54  % (16348)------------------------------
% 0.21/0.55  % (16372)Refutation not found, incomplete strategy% (16372)------------------------------
% 0.21/0.55  % (16372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (16372)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (16372)Memory used [KB]: 10746
% 0.21/0.55  % (16372)Time elapsed: 0.134 s
% 0.21/0.55  % (16372)------------------------------
% 0.21/0.55  % (16372)------------------------------
% 0.21/0.55  % (16375)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (16371)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (16373)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (16364)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (16352)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (16366)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (16356)Refutation not found, incomplete strategy% (16356)------------------------------
% 0.21/0.55  % (16356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (16356)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (16356)Memory used [KB]: 10746
% 0.21/0.55  % (16356)Time elapsed: 0.144 s
% 0.21/0.55  % (16356)------------------------------
% 0.21/0.55  % (16356)------------------------------
% 0.21/0.55  % (16367)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (16365)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (16369)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (16363)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (16363)Refutation not found, incomplete strategy% (16363)------------------------------
% 0.21/0.55  % (16363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (16363)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (16363)Memory used [KB]: 10618
% 0.21/0.55  % (16363)Time elapsed: 0.141 s
% 0.21/0.55  % (16363)------------------------------
% 0.21/0.55  % (16363)------------------------------
% 0.21/0.56  % (16358)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (16370)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (16355)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (16357)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (16359)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (16361)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (16368)Refutation not found, incomplete strategy% (16368)------------------------------
% 0.21/0.56  % (16368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (16368)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (16368)Memory used [KB]: 10746
% 0.21/0.56  % (16368)Time elapsed: 0.095 s
% 0.21/0.56  % (16368)------------------------------
% 0.21/0.56  % (16368)------------------------------
% 0.21/0.57  % (16353)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f400,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f399,f332])).
% 0.21/0.57  fof(f332,plain,(
% 0.21/0.57    k1_xboole_0 != sK2),
% 0.21/0.57    inference(backward_demodulation,[],[f44,f322])).
% 0.21/0.57  fof(f322,plain,(
% 0.21/0.57    k1_xboole_0 = sK1),
% 0.21/0.57    inference(resolution,[],[f320,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.57  fof(f320,plain,(
% 0.21/0.57    v1_xboole_0(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f319,f126])).
% 0.21/0.57  fof(f126,plain,(
% 0.21/0.57    r1_tarski(sK2,sK1)),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f124])).
% 0.21/0.57  fof(f124,plain,(
% 0.21/0.57    r1_tarski(sK2,sK1) | r1_tarski(sK2,sK1)),
% 0.21/0.57    inference(resolution,[],[f121,f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.57    inference(rectify,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.57    inference(nnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    ( ! [X1] : (r2_hidden(sK5(sK2,X1),sK1) | r1_tarski(sK2,X1)) )),
% 0.21/0.57    inference(resolution,[],[f118,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f35])).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f117,f104])).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.57    inference(resolution,[],[f101,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f35])).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    r1_tarski(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f96,f84])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    r1_tarski(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f79,f70])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.57    inference(resolution,[],[f54,f53])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(sK0)) | r1_tarski(sK1,k1_zfmisc_1(sK0))) )),
% 0.21/0.57    inference(resolution,[],[f74,f60])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK6(X0,X1),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r1_tarski(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK6(X0,X1),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r1_tarski(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.57    inference(rectify,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r1_tarski(sK1,k1_zfmisc_1(sK0))) )),
% 0.21/0.57    inference(resolution,[],[f73,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(rectify,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0))) | r1_tarski(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f64,f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.57    inference(resolution,[],[f49,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f24,f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.57    inference(nnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.57    inference(flattening,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.57    inference(negated_conjecture,[],[f9])).
% 0.21/0.57  fof(f9,conjecture,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.57    inference(flattening,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(sK0)) | r1_tarski(sK2,k1_zfmisc_1(sK0))) )),
% 0.21/0.57    inference(resolution,[],[f77,f60])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r1_tarski(sK2,k1_zfmisc_1(sK0))) )),
% 0.21/0.57    inference(resolution,[],[f76,f46])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0))) | r1_tarski(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f65,f61])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    r2_hidden(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.57    inference(resolution,[],[f49,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1) | ~r2_hidden(X0,k1_zfmisc_1(sK0))) )),
% 0.21/0.57    inference(resolution,[],[f43,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f319,plain,(
% 0.21/0.57    v1_xboole_0(sK1) | ~r1_tarski(sK2,sK1)),
% 0.21/0.57    inference(resolution,[],[f318,f60])).
% 0.21/0.57  fof(f318,plain,(
% 0.21/0.57    ~r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(sK1)),
% 0.21/0.57    inference(resolution,[],[f317,f48])).
% 0.21/0.57  fof(f317,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f314,f44])).
% 0.21/0.57  fof(f314,plain,(
% 0.21/0.57    v1_xboole_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | sK1 = sK2),
% 0.21/0.57    inference(resolution,[],[f312,f190])).
% 0.21/0.57  fof(f190,plain,(
% 0.21/0.57    ( ! [X4] : (~r2_hidden(sK4(X4,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(X4)) | sK2 = X4) )),
% 0.21/0.57    inference(resolution,[],[f51,f88])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f87,f86])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.57    inference(resolution,[],[f84,f52])).
% 0.21/0.57  fof(f87,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK2) | ~r2_hidden(X0,k1_zfmisc_1(sK0))) )),
% 0.21/0.57    inference(resolution,[],[f42,f48])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(flattening,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 0.21/0.57  fof(f312,plain,(
% 0.21/0.57    r2_hidden(sK4(sK1,sK2),sK1) | v1_xboole_0(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f310,f44])).
% 0.21/0.57  fof(f310,plain,(
% 0.21/0.57    r2_hidden(sK4(sK1,sK2),sK1) | sK1 = sK2 | v1_xboole_0(sK1)),
% 0.21/0.57    inference(resolution,[],[f286,f126])).
% 0.21/0.57  fof(f286,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | r2_hidden(sK4(X0,X1),X0) | X0 = X1 | v1_xboole_0(X0)) )),
% 0.21/0.57    inference(resolution,[],[f269,f60])).
% 0.21/0.57  fof(f269,plain,(
% 0.21/0.57    ( ! [X6,X5] : (~r2_hidden(X6,k1_zfmisc_1(X5)) | v1_xboole_0(X5) | r2_hidden(sK4(X5,X6),X5) | X5 = X6) )),
% 0.21/0.57    inference(resolution,[],[f134,f48])).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_xboole_0(X0) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.21/0.57    inference(resolution,[],[f50,f49])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    sK1 != sK2),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f399,plain,(
% 0.21/0.57    k1_xboole_0 = sK2),
% 0.21/0.57    inference(resolution,[],[f324,f45])).
% 0.21/0.57  fof(f324,plain,(
% 0.21/0.57    v1_xboole_0(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f120,f321])).
% 0.21/0.57  fof(f321,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK1)) )),
% 0.21/0.57    inference(resolution,[],[f320,f46])).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    r2_hidden(sK3(sK2),sK1) | v1_xboole_0(sK2)),
% 0.21/0.57    inference(resolution,[],[f118,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (16353)------------------------------
% 0.21/0.57  % (16353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (16353)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (16353)Memory used [KB]: 6652
% 0.21/0.57  % (16353)Time elapsed: 0.143 s
% 0.21/0.57  % (16353)------------------------------
% 0.21/0.57  % (16353)------------------------------
% 0.21/0.57  % (16344)Success in time 0.201 s
%------------------------------------------------------------------------------
