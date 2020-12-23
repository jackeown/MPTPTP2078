%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 (1661 expanded)
%              Number of leaves         :   11 ( 445 expanded)
%              Depth                    :   35
%              Number of atoms          :  273 (8126 expanded)
%              Number of equality atoms :   26 ( 910 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(subsumption_resolution,[],[f136,f128])).

fof(f128,plain,(
    r2_hidden(sK3(sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f125,f34])).

fof(f34,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( sK1 != X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK1)
              | ~ r2_hidden(X3,sK2) )
            & ( r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(f125,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | sK1 = sK2 ),
    inference(resolution,[],[f123,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1,X0),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(resolution,[],[f57,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_hidden(sK3(X1,X0),X1) ) ),
    inference(resolution,[],[f54,f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(resolution,[],[f35,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f123,plain,(
    ~ r2_hidden(sK3(sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f122,f59])).

fof(f59,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK0)
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f38,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f122,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),sK2)
    | ~ r2_hidden(sK3(sK2,sK1),sK0) ),
    inference(resolution,[],[f121,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f52,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
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

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f33,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f33,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f121,plain,(
    ~ r2_hidden(sK3(sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f120,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f38,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f120,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),sK1)
    | ~ r2_hidden(sK3(sK2,sK1),sK0) ),
    inference(subsumption_resolution,[],[f119,f98])).

fof(f98,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | ~ r2_hidden(sK3(sK2,sK1),sK0) ),
    inference(subsumption_resolution,[],[f97,f34])).

fof(f97,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),sK0)
    | r2_hidden(sK3(sK1,sK2),sK1)
    | sK1 = sK2 ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),sK0)
    | r2_hidden(sK3(sK1,sK2),sK1)
    | sK1 = sK2
    | r2_hidden(sK3(sK1,sK2),sK1) ),
    inference(resolution,[],[f92,f57])).

fof(f92,plain,
    ( r1_tarski(sK2,sK1)
    | ~ r2_hidden(sK3(sK2,sK1),sK0)
    | r2_hidden(sK3(sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f79,f34])).

fof(f79,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | sK1 = sK2
    | ~ r2_hidden(sK3(sK2,sK1),sK0)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f69,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0,sK1),sK2)
      | ~ r2_hidden(sK3(X0,sK1),sK0)
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f53,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f119,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK1)
    | ~ r2_hidden(sK3(sK2,sK1),sK1)
    | ~ r2_hidden(sK3(sK2,sK1),sK0) ),
    inference(resolution,[],[f113,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f50,f43])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f32,f40])).

fof(f32,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f113,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),sK2)
    | ~ r2_hidden(sK3(sK1,sK2),sK1) ),
    inference(resolution,[],[f110,f58])).

fof(f110,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK0)
    | ~ r2_hidden(sK3(sK2,sK1),sK2) ),
    inference(resolution,[],[f109,f59])).

fof(f109,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),sK0)
    | ~ r2_hidden(sK3(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f108,f103])).

fof(f103,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r2_hidden(sK3(sK2,sK1),sK0)
    | ~ r2_hidden(sK3(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f101,f34])).

fof(f101,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK0)
    | ~ r2_hidden(sK3(sK2,sK1),sK0)
    | ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(resolution,[],[f99,f54])).

fof(f99,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK3(sK1,sK2),sK0)
    | ~ r2_hidden(sK3(sK2,sK1),sK0) ),
    inference(resolution,[],[f98,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0,sK2),sK1)
      | ~ r2_hidden(sK3(X0,sK2),sK0)
      | r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f51,f37])).

fof(f108,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),sK0)
    | ~ r2_hidden(sK3(sK1,sK2),sK0)
    | r1_tarski(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),sK0)
    | ~ r2_hidden(sK3(sK1,sK2),sK0)
    | ~ r2_hidden(sK3(sK2,sK1),sK0)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f102,f56])).

fof(f102,plain,
    ( r2_hidden(sK3(sK2,sK1),sK2)
    | ~ r2_hidden(sK3(sK2,sK1),sK0)
    | ~ r2_hidden(sK3(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f100,f34])).

fof(f100,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK0)
    | ~ r2_hidden(sK3(sK2,sK1),sK0)
    | sK1 = sK2
    | r2_hidden(sK3(sK2,sK1),sK2) ),
    inference(resolution,[],[f99,f57])).

fof(f136,plain,(
    ~ r2_hidden(sK3(sK1,sK2),sK1) ),
    inference(resolution,[],[f134,f58])).

fof(f134,plain,(
    ~ r2_hidden(sK3(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f133,f123])).

fof(f133,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK0)
    | r2_hidden(sK3(sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f131,f34])).

fof(f131,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK0)
    | sK1 = sK2
    | r2_hidden(sK3(sK2,sK1),sK2) ),
    inference(resolution,[],[f130,f57])).

fof(f130,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK3(sK1,sK2),sK0) ),
    inference(resolution,[],[f128,f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:35:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (12507)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (12525)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (12517)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (12507)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (12509)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (12524)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f137,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f136,f128])).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    r2_hidden(sK3(sK1,sK2),sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f125,f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    sK1 != sK2),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21,f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(nnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(flattening,[],[f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.22/0.56    inference(negated_conjecture,[],[f7])).
% 0.22/0.56  fof(f7,conjecture,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    r2_hidden(sK3(sK1,sK2),sK1) | sK1 = sK2),
% 0.22/0.56    inference(resolution,[],[f123,f69])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X1,X0),X1) | r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 0.22/0.56    inference(resolution,[],[f57,f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.22/0.56    inference(unused_predicate_definition_removal,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_hidden(sK3(X1,X0),X1)) )),
% 0.22/0.56    inference(resolution,[],[f54,f36])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.56    inference(resolution,[],[f35,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.22/0.56    inference(unused_predicate_definition_removal,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,sK1),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f122,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X1] : (r2_hidden(X1,sK0) | ~r2_hidden(X1,sK2)) )),
% 0.22/0.56    inference(resolution,[],[f38,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,sK1),sK2) | ~r2_hidden(sK3(sK2,sK1),sK0)),
% 0.22/0.56    inference(resolution,[],[f121,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f52,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.56    inference(rectify,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.56    inference(nnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | v1_xboole_0(sK0)) )),
% 0.22/0.56    inference(resolution,[],[f33,f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.56    inference(nnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,sK1),sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f120,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) )),
% 0.22/0.56    inference(resolution,[],[f38,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,sK1),sK1) | ~r2_hidden(sK3(sK2,sK1),sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f119,f98])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    r2_hidden(sK3(sK1,sK2),sK1) | ~r2_hidden(sK3(sK2,sK1),sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f97,f34])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,sK1),sK0) | r2_hidden(sK3(sK1,sK2),sK1) | sK1 = sK2),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f95])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,sK1),sK0) | r2_hidden(sK3(sK1,sK2),sK1) | sK1 = sK2 | r2_hidden(sK3(sK1,sK2),sK1)),
% 0.22/0.56    inference(resolution,[],[f92,f57])).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    r1_tarski(sK2,sK1) | ~r2_hidden(sK3(sK2,sK1),sK0) | r2_hidden(sK3(sK1,sK2),sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f79,f34])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    r2_hidden(sK3(sK1,sK2),sK1) | sK1 = sK2 | ~r2_hidden(sK3(sK2,sK1),sK0) | r1_tarski(sK2,sK1)),
% 0.22/0.56    inference(resolution,[],[f69,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(sK3(X0,sK1),sK2) | ~r2_hidden(sK3(X0,sK1),sK0) | r1_tarski(X0,sK1)) )),
% 0.22/0.56    inference(resolution,[],[f53,f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK1,sK2),sK1) | ~r2_hidden(sK3(sK2,sK1),sK1) | ~r2_hidden(sK3(sK2,sK1),sK0)),
% 0.22/0.56    inference(resolution,[],[f113,f51])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f50,f43])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0) | v1_xboole_0(sK0)) )),
% 0.22/0.56    inference(resolution,[],[f32,f40])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f113,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,sK1),sK2) | ~r2_hidden(sK3(sK1,sK2),sK1)),
% 0.22/0.56    inference(resolution,[],[f110,f58])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK1,sK2),sK0) | ~r2_hidden(sK3(sK2,sK1),sK2)),
% 0.22/0.56    inference(resolution,[],[f109,f59])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,sK1),sK0) | ~r2_hidden(sK3(sK1,sK2),sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f108,f103])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    ~r1_tarski(sK2,sK1) | ~r2_hidden(sK3(sK2,sK1),sK0) | ~r2_hidden(sK3(sK1,sK2),sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f101,f34])).
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK1,sK2),sK0) | ~r2_hidden(sK3(sK2,sK1),sK0) | ~r1_tarski(sK2,sK1) | sK1 = sK2),
% 0.22/0.56    inference(resolution,[],[f99,f54])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    r1_tarski(sK1,sK2) | ~r2_hidden(sK3(sK1,sK2),sK0) | ~r2_hidden(sK3(sK2,sK1),sK0)),
% 0.22/0.56    inference(resolution,[],[f98,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(sK3(X0,sK2),sK1) | ~r2_hidden(sK3(X0,sK2),sK0) | r1_tarski(X0,sK2)) )),
% 0.22/0.56    inference(resolution,[],[f51,f37])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,sK1),sK0) | ~r2_hidden(sK3(sK1,sK2),sK0) | r1_tarski(sK2,sK1)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f107])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,sK1),sK0) | ~r2_hidden(sK3(sK1,sK2),sK0) | ~r2_hidden(sK3(sK2,sK1),sK0) | r1_tarski(sK2,sK1)),
% 0.22/0.56    inference(resolution,[],[f102,f56])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    r2_hidden(sK3(sK2,sK1),sK2) | ~r2_hidden(sK3(sK2,sK1),sK0) | ~r2_hidden(sK3(sK1,sK2),sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f100,f34])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK1,sK2),sK0) | ~r2_hidden(sK3(sK2,sK1),sK0) | sK1 = sK2 | r2_hidden(sK3(sK2,sK1),sK2)),
% 0.22/0.56    inference(resolution,[],[f99,f57])).
% 0.22/0.56  fof(f136,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK1,sK2),sK1)),
% 0.22/0.56    inference(resolution,[],[f134,f58])).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK1,sK2),sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f133,f123])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK1,sK2),sK0) | r2_hidden(sK3(sK2,sK1),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f131,f34])).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK1,sK2),sK0) | sK1 = sK2 | r2_hidden(sK3(sK2,sK1),sK2)),
% 0.22/0.56    inference(resolution,[],[f130,f57])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    r1_tarski(sK1,sK2) | ~r2_hidden(sK3(sK1,sK2),sK0)),
% 0.22/0.56    inference(resolution,[],[f128,f55])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (12507)------------------------------
% 0.22/0.56  % (12507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (12507)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (12507)Memory used [KB]: 6268
% 0.22/0.56  % (12507)Time elapsed: 0.124 s
% 0.22/0.56  % (12507)------------------------------
% 0.22/0.56  % (12507)------------------------------
% 0.22/0.56  % (12501)Success in time 0.199 s
%------------------------------------------------------------------------------
