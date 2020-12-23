%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 203 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   20
%              Number of atoms          :  322 ( 786 expanded)
%              Number of equality atoms :   51 (  98 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f825,plain,(
    $false ),
    inference(subsumption_resolution,[],[f824,f90])).

fof(f90,plain,(
    sK1 != k4_subset_1(sK1,sK2,sK1) ),
    inference(backward_demodulation,[],[f52,f53])).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f52,plain,(
    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f824,plain,(
    sK1 = k4_subset_1(sK1,sK2,sK1) ),
    inference(forward_demodulation,[],[f823,f464])).

fof(f464,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f460,f55])).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f460,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f63,f443])).

fof(f443,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f438,f303])).

fof(f303,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f301,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f301,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f300,f93])).

fof(f93,plain,(
    ! [X0] : sP0(X0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f89,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f89,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f300,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f295])).

fof(f295,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1,X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f279,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f279,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(sK3(X9),X10)
      | ~ sP0(X10,X11,X9)
      | v1_xboole_0(X9) ) ),
    inference(resolution,[],[f80,f58])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f438,plain,(
    v1_xboole_0(k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f427,f89])).

fof(f427,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK1,X1,k4_xboole_0(sK2,X0))
      | v1_xboole_0(k4_xboole_0(sK2,X0)) ) ),
    inference(duplicate_literal_removal,[],[f420])).

fof(f420,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k4_xboole_0(sK2,X0))
      | ~ sP0(sK1,X1,k4_xboole_0(sK2,X0))
      | v1_xboole_0(k4_xboole_0(sK2,X0)) ) ),
    inference(resolution,[],[f320,f279])).

fof(f320,plain,(
    ! [X14] :
      ( r2_hidden(sK3(k4_xboole_0(sK2,X14)),sK1)
      | v1_xboole_0(k4_xboole_0(sK2,X14)) ) ),
    inference(resolution,[],[f287,f216])).

fof(f216,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK2)
      | r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f69,f128])).

fof(f128,plain,(
    r1_tarski(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,
    ( r1_tarski(sK2,sK1)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f124,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(sK2,sK1) ) ),
    inference(resolution,[],[f105,f87])).

fof(f87,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r1_tarski(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( r1_tarski(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f105,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(sK1))
      | r1_tarski(sK2,sK1) ) ),
    inference(resolution,[],[f101,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f98,f88])).

fof(f88,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f98,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f64,f51])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

% (10668)Refutation not found, incomplete strategy% (10668)------------------------------
% (10668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10668)Termination reason: Refutation not found, incomplete strategy

% (10668)Memory used [KB]: 10746
% (10668)Time elapsed: 0.180 s
% (10668)------------------------------
% (10668)------------------------------
fof(f36,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f124,plain,(
    ! [X4] :
      ( r1_tarski(k1_zfmisc_1(sK1),X4)
      | r1_tarski(sK2,sK1) ) ),
    inference(resolution,[],[f70,f105])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f287,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k4_xboole_0(X0,X1)),X0)
      | v1_xboole_0(k4_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f272,f89])).

fof(f272,plain,(
    ! [X10,X11,X9] :
      ( ~ sP0(X11,X10,X9)
      | r2_hidden(sK3(X9),X10)
      | v1_xboole_0(X9) ) ),
    inference(resolution,[],[f79,f58])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f823,plain,(
    k4_subset_1(sK1,sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f820,f145])).

fof(f145,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f96,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f96,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f61,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f820,plain,(
    k4_subset_1(sK1,sK2,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f816,f91])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f56,f53])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f816,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | k4_subset_1(sK1,sK2,X0) = k2_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f78,f51])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:11:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (10679)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (10679)Refutation not found, incomplete strategy% (10679)------------------------------
% 0.21/0.50  % (10679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10663)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (10679)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (10679)Memory used [KB]: 10746
% 0.21/0.50  % (10679)Time elapsed: 0.075 s
% 0.21/0.50  % (10679)------------------------------
% 0.21/0.50  % (10679)------------------------------
% 0.21/0.51  % (10657)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (10657)Refutation not found, incomplete strategy% (10657)------------------------------
% 0.21/0.51  % (10657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10657)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10657)Memory used [KB]: 1663
% 0.21/0.51  % (10657)Time elapsed: 0.104 s
% 0.21/0.51  % (10657)------------------------------
% 0.21/0.51  % (10657)------------------------------
% 0.21/0.51  % (10665)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (10664)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (10658)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (10669)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (10685)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (10678)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (10661)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (10678)Refutation not found, incomplete strategy% (10678)------------------------------
% 0.21/0.53  % (10678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10678)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10678)Memory used [KB]: 1791
% 0.21/0.53  % (10678)Time elapsed: 0.096 s
% 0.21/0.53  % (10678)------------------------------
% 0.21/0.53  % (10678)------------------------------
% 0.21/0.53  % (10673)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (10682)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (10670)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (10660)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (10677)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (10662)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (10659)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (10680)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (10674)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (10674)Refutation not found, incomplete strategy% (10674)------------------------------
% 0.21/0.55  % (10674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10674)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10674)Memory used [KB]: 10618
% 0.21/0.55  % (10674)Time elapsed: 0.140 s
% 0.21/0.55  % (10674)------------------------------
% 0.21/0.55  % (10674)------------------------------
% 0.21/0.55  % (10686)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (10675)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (10672)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (10684)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (10666)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (10666)Refutation not found, incomplete strategy% (10666)------------------------------
% 0.21/0.56  % (10666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10667)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (10676)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (10666)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10666)Memory used [KB]: 10618
% 0.21/0.56  % (10666)Time elapsed: 0.148 s
% 0.21/0.56  % (10666)------------------------------
% 0.21/0.56  % (10666)------------------------------
% 0.21/0.56  % (10667)Refutation not found, incomplete strategy% (10667)------------------------------
% 0.21/0.56  % (10667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10667)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10667)Memory used [KB]: 10618
% 0.21/0.56  % (10667)Time elapsed: 0.161 s
% 0.21/0.56  % (10667)------------------------------
% 0.21/0.56  % (10667)------------------------------
% 0.21/0.56  % (10668)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (10681)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (10683)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.57  % (10683)Refutation not found, incomplete strategy% (10683)------------------------------
% 0.21/0.57  % (10683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (10683)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (10683)Memory used [KB]: 10746
% 0.21/0.57  % (10683)Time elapsed: 0.159 s
% 0.21/0.57  % (10683)------------------------------
% 0.21/0.57  % (10683)------------------------------
% 0.21/0.57  % (10671)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (10664)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f825,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(subsumption_resolution,[],[f824,f90])).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    sK1 != k4_subset_1(sK1,sK2,sK1)),
% 0.21/0.58    inference(backward_demodulation,[],[f52,f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,axiom,(
% 0.21/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))),
% 0.21/0.58    inference(cnf_transformation,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f20])).
% 0.21/0.58  fof(f20,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.21/0.58    inference(negated_conjecture,[],[f19])).
% 0.21/0.58  fof(f19,conjecture,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 0.21/0.58  fof(f824,plain,(
% 0.21/0.58    sK1 = k4_subset_1(sK1,sK2,sK1)),
% 0.21/0.58    inference(forward_demodulation,[],[f823,f464])).
% 0.21/0.58  fof(f464,plain,(
% 0.21/0.58    sK1 = k2_xboole_0(sK1,sK2)),
% 0.21/0.58    inference(forward_demodulation,[],[f460,f55])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.58  fof(f460,plain,(
% 0.21/0.58    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.58    inference(superposition,[],[f63,f443])).
% 0.21/0.58  fof(f443,plain,(
% 0.21/0.58    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 0.21/0.58    inference(resolution,[],[f438,f303])).
% 0.21/0.58  fof(f303,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(resolution,[],[f301,f76])).
% 0.21/0.58  fof(f76,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.58  fof(f301,plain,(
% 0.21/0.58    v1_xboole_0(k1_xboole_0)),
% 0.21/0.58    inference(resolution,[],[f300,f93])).
% 0.21/0.58  fof(f93,plain,(
% 0.21/0.58    ( ! [X0] : (sP0(X0,k1_xboole_0,k1_xboole_0)) )),
% 0.21/0.58    inference(superposition,[],[f89,f54])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.58  fof(f89,plain,(
% 0.21/0.58    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(equality_resolution,[],[f85])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.58    inference(nnf_transformation,[],[f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.58    inference(definition_folding,[],[f3,f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.58  fof(f300,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~sP0(X0,X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f295])).
% 0.21/0.58  fof(f295,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~sP0(X0,X1,X0) | v1_xboole_0(X0) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(resolution,[],[f279,f58])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.58    inference(rectify,[],[f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.58    inference(nnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.58  fof(f279,plain,(
% 0.21/0.58    ( ! [X10,X11,X9] : (~r2_hidden(sK3(X9),X10) | ~sP0(X10,X11,X9) | v1_xboole_0(X9)) )),
% 0.21/0.58    inference(resolution,[],[f80,f58])).
% 0.21/0.58  fof(f80,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f47,f48])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.58    inference(rectify,[],[f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.58    inference(flattening,[],[f45])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.58    inference(nnf_transformation,[],[f28])).
% 0.21/0.58  fof(f438,plain,(
% 0.21/0.58    v1_xboole_0(k4_xboole_0(sK2,sK1))),
% 0.21/0.58    inference(resolution,[],[f427,f89])).
% 0.21/0.58  fof(f427,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~sP0(sK1,X1,k4_xboole_0(sK2,X0)) | v1_xboole_0(k4_xboole_0(sK2,X0))) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f420])).
% 0.21/0.58  fof(f420,plain,(
% 0.21/0.58    ( ! [X0,X1] : (v1_xboole_0(k4_xboole_0(sK2,X0)) | ~sP0(sK1,X1,k4_xboole_0(sK2,X0)) | v1_xboole_0(k4_xboole_0(sK2,X0))) )),
% 0.21/0.58    inference(resolution,[],[f320,f279])).
% 0.21/0.58  fof(f320,plain,(
% 0.21/0.58    ( ! [X14] : (r2_hidden(sK3(k4_xboole_0(sK2,X14)),sK1) | v1_xboole_0(k4_xboole_0(sK2,X14))) )),
% 0.21/0.58    inference(resolution,[],[f287,f216])).
% 0.21/0.58  fof(f216,plain,(
% 0.21/0.58    ( ! [X2] : (~r2_hidden(X2,sK2) | r2_hidden(X2,sK1)) )),
% 0.21/0.58    inference(resolution,[],[f69,f128])).
% 0.21/0.58  fof(f128,plain,(
% 0.21/0.58    r1_tarski(sK2,sK1)),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f127])).
% 0.21/0.58  fof(f127,plain,(
% 0.21/0.58    r1_tarski(sK2,sK1) | r1_tarski(sK2,sK1)),
% 0.21/0.58    inference(resolution,[],[f124,f113])).
% 0.21/0.58  fof(f113,plain,(
% 0.21/0.58    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(sK2,sK1)) )),
% 0.21/0.58    inference(resolution,[],[f105,f87])).
% 0.21/0.58  fof(f87,plain,(
% 0.21/0.58    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.58    inference(equality_resolution,[],[f73])).
% 0.21/0.58  fof(f73,plain,(
% 0.21/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f44])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.58    inference(rectify,[],[f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.58    inference(nnf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.58  fof(f105,plain,(
% 0.21/0.58    ( ! [X3] : (~r2_hidden(X3,k1_zfmisc_1(sK1)) | r1_tarski(sK2,sK1)) )),
% 0.21/0.58    inference(resolution,[],[f101,f57])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f101,plain,(
% 0.21/0.58    v1_xboole_0(k1_zfmisc_1(sK1)) | r1_tarski(sK2,sK1)),
% 0.21/0.58    inference(resolution,[],[f98,f88])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.21/0.58    inference(equality_resolution,[],[f72])).
% 0.21/0.58  fof(f72,plain,(
% 0.21/0.58    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f44])).
% 0.21/0.58  fof(f98,plain,(
% 0.21/0.58    r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1))),
% 0.21/0.58    inference(resolution,[],[f64,f51])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.21/0.58    inference(cnf_transformation,[],[f31])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f36])).
% 1.76/0.58  % (10668)Refutation not found, incomplete strategy% (10668)------------------------------
% 1.76/0.58  % (10668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.58  % (10668)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.58  
% 1.76/0.58  % (10668)Memory used [KB]: 10746
% 1.76/0.58  % (10668)Time elapsed: 0.180 s
% 1.76/0.58  % (10668)------------------------------
% 1.76/0.58  % (10668)------------------------------
% 1.76/0.58  fof(f36,plain,(
% 1.76/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.76/0.58    inference(nnf_transformation,[],[f22])).
% 1.76/0.58  fof(f22,plain,(
% 1.76/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.76/0.58    inference(ennf_transformation,[],[f15])).
% 1.76/0.58  fof(f15,axiom,(
% 1.76/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.76/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.76/0.58  fof(f124,plain,(
% 1.76/0.58    ( ! [X4] : (r1_tarski(k1_zfmisc_1(sK1),X4) | r1_tarski(sK2,sK1)) )),
% 1.76/0.58    inference(resolution,[],[f70,f105])).
% 1.76/0.58  fof(f70,plain,(
% 1.76/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.76/0.58    inference(cnf_transformation,[],[f40])).
% 1.76/0.58  fof(f40,plain,(
% 1.76/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.76/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).
% 1.76/0.58  fof(f39,plain,(
% 1.76/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.76/0.58    introduced(choice_axiom,[])).
% 1.76/0.58  fof(f38,plain,(
% 1.76/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.76/0.58    inference(rectify,[],[f37])).
% 1.76/0.58  fof(f37,plain,(
% 1.76/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.76/0.58    inference(nnf_transformation,[],[f24])).
% 1.76/0.58  fof(f24,plain,(
% 1.76/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.76/0.58    inference(ennf_transformation,[],[f2])).
% 1.76/0.58  fof(f2,axiom,(
% 1.76/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.76/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.76/0.58  fof(f69,plain,(
% 1.76/0.58    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.76/0.58    inference(cnf_transformation,[],[f40])).
% 1.76/0.58  fof(f287,plain,(
% 1.76/0.58    ( ! [X0,X1] : (r2_hidden(sK3(k4_xboole_0(X0,X1)),X0) | v1_xboole_0(k4_xboole_0(X0,X1))) )),
% 1.76/0.58    inference(resolution,[],[f272,f89])).
% 1.76/0.59  fof(f272,plain,(
% 1.76/0.59    ( ! [X10,X11,X9] : (~sP0(X11,X10,X9) | r2_hidden(sK3(X9),X10) | v1_xboole_0(X9)) )),
% 1.76/0.59    inference(resolution,[],[f79,f58])).
% 1.76/0.60  fof(f79,plain,(
% 1.76/0.60    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f49])).
% 1.76/0.60  fof(f63,plain,(
% 1.76/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f6])).
% 1.76/0.60  fof(f6,axiom,(
% 1.76/0.60    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.76/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.76/0.60  fof(f823,plain,(
% 1.76/0.60    k4_subset_1(sK1,sK2,sK1) = k2_xboole_0(sK1,sK2)),
% 1.76/0.60    inference(forward_demodulation,[],[f820,f145])).
% 1.76/0.60  fof(f145,plain,(
% 1.76/0.60    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.76/0.60    inference(superposition,[],[f96,f61])).
% 1.76/0.60  fof(f61,plain,(
% 1.76/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.76/0.60    inference(cnf_transformation,[],[f14])).
% 1.76/0.60  fof(f14,axiom,(
% 1.76/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.76/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.76/0.60  fof(f96,plain,(
% 1.76/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 1.76/0.60    inference(superposition,[],[f61,f59])).
% 1.76/0.60  fof(f59,plain,(
% 1.76/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f10])).
% 1.76/0.60  fof(f10,axiom,(
% 1.76/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.76/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.76/0.60  fof(f820,plain,(
% 1.76/0.60    k4_subset_1(sK1,sK2,sK1) = k2_xboole_0(sK2,sK1)),
% 1.76/0.60    inference(resolution,[],[f816,f91])).
% 1.76/0.60  fof(f91,plain,(
% 1.76/0.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.76/0.60    inference(forward_demodulation,[],[f56,f53])).
% 1.76/0.60  fof(f56,plain,(
% 1.76/0.60    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.76/0.60    inference(cnf_transformation,[],[f17])).
% 1.76/0.60  fof(f17,axiom,(
% 1.76/0.60    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.76/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.76/0.60  fof(f816,plain,(
% 1.76/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | k4_subset_1(sK1,sK2,X0) = k2_xboole_0(sK2,X0)) )),
% 1.76/0.60    inference(resolution,[],[f78,f51])).
% 1.76/0.60  fof(f78,plain,(
% 1.76/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f27])).
% 1.76/0.60  fof(f27,plain,(
% 1.76/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.76/0.60    inference(flattening,[],[f26])).
% 1.76/0.60  fof(f26,plain,(
% 1.76/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.76/0.60    inference(ennf_transformation,[],[f18])).
% 1.76/0.60  fof(f18,axiom,(
% 1.76/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.76/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.76/0.60  % SZS output end Proof for theBenchmark
% 1.76/0.60  % (10664)------------------------------
% 1.76/0.60  % (10664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (10664)Termination reason: Refutation
% 1.76/0.60  
% 1.76/0.60  % (10664)Memory used [KB]: 6780
% 1.76/0.60  % (10664)Time elapsed: 0.157 s
% 1.76/0.60  % (10664)------------------------------
% 1.76/0.60  % (10664)------------------------------
% 1.76/0.60  % (10656)Success in time 0.231 s
%------------------------------------------------------------------------------
