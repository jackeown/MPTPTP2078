%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 403 expanded)
%              Number of leaves         :   12 ( 105 expanded)
%              Depth                    :   23
%              Number of atoms          :  266 (1967 expanded)
%              Number of equality atoms :   28 ( 176 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f354,plain,(
    $false ),
    inference(subsumption_resolution,[],[f352,f329])).

fof(f329,plain,(
    k1_xboole_0 != sK2 ),
    inference(backward_demodulation,[],[f37,f325])).

fof(f325,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f320,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f38,f57])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f320,plain,(
    v1_xboole_0(sK1) ),
    inference(resolution,[],[f248,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f55,f57])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f248,plain,(
    m1_subset_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f33,f246])).

fof(f246,plain,(
    k1_xboole_0 = k1_zfmisc_1(sK0) ),
    inference(resolution,[],[f242,f61])).

fof(f242,plain,(
    v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f241,f228])).

fof(f228,plain,
    ( ~ r1_tarski(sK2,sK1)
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f227,f37])).

fof(f227,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(resolution,[],[f225,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f225,plain,
    ( r1_tarski(sK1,sK2)
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,
    ( r1_tarski(sK1,sK2)
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f217,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f217,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | r1_tarski(sK1,X0)
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f96,f151])).

fof(f151,plain,(
    ! [X11] :
      ( r2_hidden(sK3(sK1,X11),sK0)
      | r1_tarski(sK1,X11)
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f93,f78])).

fof(f78,plain,
    ( r1_tarski(sK1,sK0)
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f76,f43])).

fof(f43,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f76,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f72,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f72,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f53,f33])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK3(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f49,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK1,X0),sK0)
      | r2_hidden(sK3(sK1,X0),sK2)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f82,f50])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f35,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f54,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).

fof(f22,plain,
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

fof(f23,plain,
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

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f241,plain,
    ( r1_tarski(sK2,sK1)
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f234])).

fof(f234,plain,
    ( r1_tarski(sK2,sK1)
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f233,f51])).

fof(f233,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),sK1)
      | r1_tarski(sK2,X0)
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),sK1)
      | r1_tarski(sK2,X0)
      | r1_tarski(sK2,X0)
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f97,f152])).

fof(f152,plain,(
    ! [X12] :
      ( r2_hidden(sK3(sK2,X12),sK0)
      | r1_tarski(sK2,X12)
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f93,f81])).

fof(f81,plain,
    ( r1_tarski(sK2,sK0)
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f79,f43])).

fof(f79,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r1_tarski(sK2,k3_tarski(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f73,f52])).

fof(f73,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f53,f34])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK2,X0),sK0)
      | r2_hidden(sK3(sK2,X0),sK1)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f83,f50])).

fof(f83,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f36,f60])).

fof(f36,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f352,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f347,f61])).

fof(f347,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f249,f63])).

fof(f249,plain,(
    m1_subset_1(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f34,f246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (5078)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (5096)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (5088)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (5078)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (5076)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (5082)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (5086)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (5094)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (5094)Refutation not found, incomplete strategy% (5094)------------------------------
% 0.22/0.52  % (5094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (5077)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (5094)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (5094)Memory used [KB]: 1663
% 0.22/0.52  % (5094)Time elapsed: 0.105 s
% 0.22/0.52  % (5094)------------------------------
% 0.22/0.52  % (5094)------------------------------
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f354,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f352,f329])).
% 0.22/0.52  fof(f329,plain,(
% 0.22/0.52    k1_xboole_0 != sK2),
% 0.22/0.52    inference(backward_demodulation,[],[f37,f325])).
% 0.22/0.52  fof(f325,plain,(
% 0.22/0.52    k1_xboole_0 = sK1),
% 0.22/0.52    inference(resolution,[],[f320,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(resolution,[],[f38,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.52  fof(f320,plain,(
% 0.22/0.52    v1_xboole_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f248,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f55,f57])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.52  fof(f248,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_xboole_0)),
% 0.22/0.52    inference(backward_demodulation,[],[f33,f246])).
% 0.22/0.52  fof(f246,plain,(
% 0.22/0.52    k1_xboole_0 = k1_zfmisc_1(sK0)),
% 0.22/0.52    inference(resolution,[],[f242,f61])).
% 0.22/0.52  fof(f242,plain,(
% 0.22/0.52    v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f241,f228])).
% 0.22/0.52  fof(f228,plain,(
% 0.22/0.52    ~r1_tarski(sK2,sK1) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f227,f37])).
% 0.22/0.52  fof(f227,plain,(
% 0.22/0.52    v1_xboole_0(k1_zfmisc_1(sK0)) | ~r1_tarski(sK2,sK1) | sK1 = sK2),
% 0.22/0.52    inference(resolution,[],[f225,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f225,plain,(
% 0.22/0.52    r1_tarski(sK1,sK2) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f218])).
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    r1_tarski(sK1,sK2) | v1_xboole_0(k1_zfmisc_1(sK0)) | r1_tarski(sK1,sK2)),
% 0.22/0.52    inference(resolution,[],[f217,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.52  fof(f217,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3(sK1,X0),sK2) | r1_tarski(sK1,X0) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f216])).
% 0.22/0.52  fof(f216,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3(sK1,X0),sK2) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 0.22/0.52    inference(resolution,[],[f96,f151])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    ( ! [X11] : (r2_hidden(sK3(sK1,X11),sK0) | r1_tarski(sK1,X11) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 0.22/0.52    inference(resolution,[],[f93,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    r1_tarski(sK1,sK0) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(forward_demodulation,[],[f76,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    v1_xboole_0(k1_zfmisc_1(sK0)) | r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0)))),
% 0.22/0.52    inference(resolution,[],[f72,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(resolution,[],[f53,f33])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK3(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f49,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK3(sK1,X0),sK0) | r2_hidden(sK3(sK1,X0),sK2) | r1_tarski(sK1,X0)) )),
% 0.22/0.52    inference(resolution,[],[f82,f50])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) )),
% 0.22/0.52    inference(resolution,[],[f35,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f54,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.22/0.52    inference(negated_conjecture,[],[f11])).
% 0.22/0.52  fof(f11,conjecture,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    r1_tarski(sK2,sK1) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f234])).
% 0.22/0.52  fof(f234,plain,(
% 0.22/0.52    r1_tarski(sK2,sK1) | v1_xboole_0(k1_zfmisc_1(sK0)) | r1_tarski(sK2,sK1)),
% 0.22/0.52    inference(resolution,[],[f233,f51])).
% 0.22/0.52  fof(f233,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3(sK2,X0),sK1) | r1_tarski(sK2,X0) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f232])).
% 0.22/0.52  fof(f232,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3(sK2,X0),sK1) | r1_tarski(sK2,X0) | r1_tarski(sK2,X0) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 0.22/0.52    inference(resolution,[],[f97,f152])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    ( ! [X12] : (r2_hidden(sK3(sK2,X12),sK0) | r1_tarski(sK2,X12) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 0.22/0.52    inference(resolution,[],[f93,f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    r1_tarski(sK2,sK0) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(forward_demodulation,[],[f79,f43])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    v1_xboole_0(k1_zfmisc_1(sK0)) | r1_tarski(sK2,k3_tarski(k1_zfmisc_1(sK0)))),
% 0.22/0.52    inference(resolution,[],[f73,f52])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(resolution,[],[f53,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK3(sK2,X0),sK0) | r2_hidden(sK3(sK2,X0),sK1) | r1_tarski(sK2,X0)) )),
% 0.22/0.52    inference(resolution,[],[f83,f50])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.22/0.52    inference(resolution,[],[f36,f60])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    sK1 != sK2),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f352,plain,(
% 0.22/0.52    k1_xboole_0 = sK2),
% 0.22/0.52    inference(resolution,[],[f347,f61])).
% 0.22/0.52  fof(f347,plain,(
% 0.22/0.52    v1_xboole_0(sK2)),
% 0.22/0.52    inference(resolution,[],[f249,f63])).
% 0.22/0.52  fof(f249,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_xboole_0)),
% 0.22/0.52    inference(backward_demodulation,[],[f34,f246])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (5078)------------------------------
% 0.22/0.52  % (5078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (5078)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (5078)Memory used [KB]: 6396
% 0.22/0.52  % (5078)Time elapsed: 0.093 s
% 0.22/0.52  % (5078)------------------------------
% 0.22/0.52  % (5078)------------------------------
% 0.22/0.53  % (5069)Success in time 0.164 s
%------------------------------------------------------------------------------
