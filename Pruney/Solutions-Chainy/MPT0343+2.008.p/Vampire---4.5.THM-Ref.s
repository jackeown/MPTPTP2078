%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:41 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 790 expanded)
%              Number of leaves         :   13 ( 206 expanded)
%              Depth                    :   27
%              Number of atoms          :  334 (4058 expanded)
%              Number of equality atoms :   27 ( 316 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f793,plain,(
    $false ),
    inference(subsumption_resolution,[],[f791,f403])).

fof(f403,plain,(
    ~ r2_hidden(sK6(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f399,f381])).

fof(f381,plain,(
    ~ r2_hidden(sK6(sK1,sK2),sK1) ),
    inference(resolution,[],[f379,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK6(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f33])).

% (612)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK6(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f379,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f377,f39])).

fof(f39,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16,f15])).

fof(f15,plain,
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

fof(f16,plain,
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

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f377,plain,
    ( r2_xboole_0(sK1,sK2)
    | sK1 = sK2 ),
    inference(resolution,[],[f375,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f375,plain,(
    r1_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f371])).

fof(f371,plain,
    ( r1_tarski(sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f365,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

% (628)Refutation not found, incomplete strategy% (628)------------------------------
% (628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (628)Termination reason: Refutation not found, incomplete strategy

% (628)Memory used [KB]: 10746
% (628)Time elapsed: 0.149 s
% (628)------------------------------
% (628)------------------------------
fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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

% (629)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f365,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK1,X1),sK2)
      | r1_tarski(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f362,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f362,plain,(
    ! [X1] :
      ( r1_tarski(sK1,X1)
      | ~ r2_hidden(sK4(sK1,X1),sK1)
      | r2_hidden(sK4(sK1,X1),sK2) ) ),
    inference(resolution,[],[f262,f37])).

fof(f37,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f262,plain,(
    ! [X2] :
      ( m1_subset_1(sK4(sK1,X2),sK0)
      | r1_tarski(sK1,X2) ) ),
    inference(subsumption_resolution,[],[f259,f231])).

fof(f231,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(sK0)
      | r1_tarski(sK1,X3) ) ),
    inference(resolution,[],[f217,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
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

fof(f217,plain,(
    ! [X3] :
      ( r2_hidden(sK3(sK0),sK0)
      | r1_tarski(sK1,X3) ) ),
    inference(resolution,[],[f201,f47])).

fof(f201,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK1)
      | r2_hidden(sK3(sK0),sK0) ) ),
    inference(resolution,[],[f197,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f197,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(resolution,[],[f193,f40])).

fof(f193,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f190,f40])).

fof(f190,plain,
    ( r2_hidden(sK3(sK1),sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f185,f62])).

fof(f62,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f35,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f185,plain,
    ( r2_hidden(sK3(sK1),sK0)
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f93,f41])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0)
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f83,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,
    ( r1_tarski(sK1,sK0)
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f61,f60])).

fof(f60,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f61,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f35,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f259,plain,(
    ! [X2] :
      ( r1_tarski(sK1,X2)
      | m1_subset_1(sK4(sK1,X2),sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f247,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f247,plain,(
    ! [X3] :
      ( r2_hidden(sK4(sK1,X3),sK0)
      | r1_tarski(sK1,X3) ) ),
    inference(resolution,[],[f243,f47])).

fof(f243,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f242,f40])).

fof(f242,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | v1_xboole_0(sK1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | v1_xboole_0(sK1)
      | ~ r2_hidden(X0,sK1)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f189,f43])).

fof(f189,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK1)
      | r2_hidden(X2,sK0)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f184,f62])).

fof(f184,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK0)
      | v1_xboole_0(k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X2,sK1)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f93,f42])).

fof(f399,plain,
    ( r2_hidden(sK6(sK1,sK2),sK1)
    | ~ r2_hidden(sK6(sK1,sK2),sK0) ),
    inference(resolution,[],[f380,f154])).

fof(f154,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f152,f40])).

fof(f152,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f38,f43])).

% (614)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f38,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f380,plain,(
    r2_hidden(sK6(sK1,sK2),sK2) ),
    inference(resolution,[],[f379,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f791,plain,(
    r2_hidden(sK6(sK1,sK2),sK0) ),
    inference(resolution,[],[f770,f380])).

fof(f770,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f761,f46])).

% (629)Refutation not found, incomplete strategy% (629)------------------------------
% (629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f761,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f754,f60])).

% (629)Termination reason: Refutation not found, incomplete strategy

% (634)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (629)Memory used [KB]: 1663
% (629)Time elapsed: 0.161 s
% (629)------------------------------
% (629)------------------------------
fof(f754,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f276,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f276,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f273,f42])).

fof(f273,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f267,f40])).

fof(f267,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f261,f59])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f261,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f247,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (621)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (630)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (609)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (609)Refutation not found, incomplete strategy% (609)------------------------------
% 0.21/0.50  % (609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (609)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (609)Memory used [KB]: 10746
% 0.21/0.50  % (609)Time elapsed: 0.094 s
% 0.21/0.50  % (609)------------------------------
% 0.21/0.50  % (609)------------------------------
% 0.21/0.51  % (624)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (617)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (617)Refutation not found, incomplete strategy% (617)------------------------------
% 0.21/0.51  % (617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (617)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (617)Memory used [KB]: 10618
% 0.21/0.51  % (617)Time elapsed: 0.110 s
% 0.21/0.51  % (617)------------------------------
% 0.21/0.51  % (617)------------------------------
% 0.21/0.52  % (630)Refutation not found, incomplete strategy% (630)------------------------------
% 0.21/0.52  % (630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (615)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (631)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (608)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (615)Refutation not found, incomplete strategy% (615)------------------------------
% 0.21/0.53  % (615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (611)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (622)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (611)Refutation not found, incomplete strategy% (611)------------------------------
% 0.21/0.54  % (611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (611)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (611)Memory used [KB]: 6268
% 0.21/0.54  % (611)Time elapsed: 0.125 s
% 0.21/0.54  % (611)------------------------------
% 0.21/0.54  % (611)------------------------------
% 0.21/0.54  % (615)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  % (637)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  
% 1.36/0.54  % (615)Memory used [KB]: 10746
% 1.36/0.54  % (615)Time elapsed: 0.118 s
% 1.36/0.54  % (615)------------------------------
% 1.36/0.54  % (615)------------------------------
% 1.36/0.55  % (630)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (630)Memory used [KB]: 10874
% 1.36/0.55  % (630)Time elapsed: 0.101 s
% 1.36/0.55  % (630)------------------------------
% 1.36/0.55  % (630)------------------------------
% 1.36/0.55  % (626)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.55  % (623)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.55  % (613)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.55  % (619)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.55  % (616)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.55  % (628)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.55  % (631)Refutation found. Thanks to Tanya!
% 1.36/0.55  % SZS status Theorem for theBenchmark
% 1.52/0.56  % (607)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.52/0.56  % (620)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.52/0.56  % (639)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.52/0.56  % (636)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.52/0.56  % (638)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.52/0.56  % (610)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.52/0.56  % (635)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.52/0.56  % (636)Refutation not found, incomplete strategy% (636)------------------------------
% 1.52/0.56  % (636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (636)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (636)Memory used [KB]: 10746
% 1.52/0.56  % (636)Time elapsed: 0.160 s
% 1.52/0.56  % (636)------------------------------
% 1.52/0.56  % (636)------------------------------
% 1.52/0.56  % SZS output start Proof for theBenchmark
% 1.52/0.56  fof(f793,plain,(
% 1.52/0.56    $false),
% 1.52/0.56    inference(subsumption_resolution,[],[f791,f403])).
% 1.52/0.56  fof(f403,plain,(
% 1.52/0.56    ~r2_hidden(sK6(sK1,sK2),sK0)),
% 1.52/0.56    inference(subsumption_resolution,[],[f399,f381])).
% 1.52/0.56  fof(f381,plain,(
% 1.52/0.56    ~r2_hidden(sK6(sK1,sK2),sK1)),
% 1.52/0.56    inference(resolution,[],[f379,f57])).
% 1.52/0.56  fof(f57,plain,(
% 1.52/0.56    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f34])).
% 1.52/0.56  fof(f34,plain,(
% 1.52/0.56    ! [X0,X1] : ((~r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK6(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 1.52/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f33])).
% 1.52/0.57  % (612)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.52/0.57  fof(f33,plain,(
% 1.52/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK6(X0,X1),X1)))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f13,plain,(
% 1.52/0.57    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f4])).
% 1.52/0.57  fof(f4,axiom,(
% 1.52/0.57    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 1.52/0.57  fof(f379,plain,(
% 1.52/0.57    r2_xboole_0(sK1,sK2)),
% 1.52/0.57    inference(subsumption_resolution,[],[f377,f39])).
% 1.52/0.57  fof(f39,plain,(
% 1.52/0.57    sK1 != sK2),
% 1.52/0.57    inference(cnf_transformation,[],[f17])).
% 1.52/0.57  fof(f17,plain,(
% 1.52/0.57    (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16,f15])).
% 1.52/0.57  fof(f15,plain,(
% 1.52/0.57    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f16,plain,(
% 1.52/0.57    ? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f14,plain,(
% 1.52/0.57    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.52/0.57    inference(nnf_transformation,[],[f10])).
% 1.52/0.57  fof(f10,plain,(
% 1.52/0.57    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.52/0.57    inference(flattening,[],[f9])).
% 1.52/0.57  fof(f9,plain,(
% 1.52/0.57    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f8])).
% 1.52/0.57  fof(f8,negated_conjecture,(
% 1.52/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.52/0.57    inference(negated_conjecture,[],[f7])).
% 1.52/0.57  fof(f7,conjecture,(
% 1.52/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 1.52/0.57  fof(f377,plain,(
% 1.52/0.57    r2_xboole_0(sK1,sK2) | sK1 = sK2),
% 1.52/0.57    inference(resolution,[],[f375,f51])).
% 1.52/0.57  fof(f51,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f28])).
% 1.52/0.57  fof(f28,plain,(
% 1.52/0.57    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.52/0.57    inference(flattening,[],[f27])).
% 1.52/0.57  fof(f27,plain,(
% 1.52/0.57    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.52/0.57    inference(nnf_transformation,[],[f3])).
% 1.52/0.57  fof(f3,axiom,(
% 1.52/0.57    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.52/0.57  fof(f375,plain,(
% 1.52/0.57    r1_tarski(sK1,sK2)),
% 1.52/0.57    inference(duplicate_literal_removal,[],[f371])).
% 1.52/0.57  fof(f371,plain,(
% 1.52/0.57    r1_tarski(sK1,sK2) | r1_tarski(sK1,sK2)),
% 1.52/0.57    inference(resolution,[],[f365,f48])).
% 1.52/0.57  fof(f48,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f26])).
% 1.52/0.57  % (628)Refutation not found, incomplete strategy% (628)------------------------------
% 1.52/0.57  % (628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (628)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (628)Memory used [KB]: 10746
% 1.52/0.57  % (628)Time elapsed: 0.149 s
% 1.52/0.57  % (628)------------------------------
% 1.52/0.57  % (628)------------------------------
% 1.52/0.57  fof(f26,plain,(
% 1.52/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.57    inference(rectify,[],[f23])).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.57    inference(nnf_transformation,[],[f12])).
% 1.52/0.57  fof(f12,plain,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.52/0.57  % (629)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.52/0.57  fof(f365,plain,(
% 1.52/0.57    ( ! [X1] : (r2_hidden(sK4(sK1,X1),sK2) | r1_tarski(sK1,X1)) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f362,f47])).
% 1.52/0.57  fof(f47,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f26])).
% 1.52/0.57  fof(f362,plain,(
% 1.52/0.57    ( ! [X1] : (r1_tarski(sK1,X1) | ~r2_hidden(sK4(sK1,X1),sK1) | r2_hidden(sK4(sK1,X1),sK2)) )),
% 1.52/0.57    inference(resolution,[],[f262,f37])).
% 1.52/0.57  fof(f37,plain,(
% 1.52/0.57    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f17])).
% 1.52/0.57  fof(f262,plain,(
% 1.52/0.57    ( ! [X2] : (m1_subset_1(sK4(sK1,X2),sK0) | r1_tarski(sK1,X2)) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f259,f231])).
% 1.52/0.57  fof(f231,plain,(
% 1.52/0.57    ( ! [X3] : (~v1_xboole_0(sK0) | r1_tarski(sK1,X3)) )),
% 1.52/0.57    inference(resolution,[],[f217,f40])).
% 1.52/0.57  fof(f40,plain,(
% 1.52/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f21])).
% 1.52/0.57  fof(f21,plain,(
% 1.52/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 1.52/0.57  fof(f20,plain,(
% 1.52/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f19,plain,(
% 1.52/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.57    inference(rectify,[],[f18])).
% 1.52/0.57  fof(f18,plain,(
% 1.52/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.57    inference(nnf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.52/0.57  fof(f217,plain,(
% 1.52/0.57    ( ! [X3] : (r2_hidden(sK3(sK0),sK0) | r1_tarski(sK1,X3)) )),
% 1.52/0.57    inference(resolution,[],[f201,f47])).
% 1.52/0.57  fof(f201,plain,(
% 1.52/0.57    ( ! [X6] : (~r2_hidden(X6,sK1) | r2_hidden(sK3(sK0),sK0)) )),
% 1.52/0.57    inference(resolution,[],[f197,f41])).
% 1.52/0.57  fof(f41,plain,(
% 1.52/0.57    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f21])).
% 1.52/0.57  fof(f197,plain,(
% 1.52/0.57    ( ! [X3] : (~v1_xboole_0(sK0) | ~r2_hidden(X3,sK1)) )),
% 1.52/0.57    inference(resolution,[],[f193,f40])).
% 1.52/0.57  fof(f193,plain,(
% 1.52/0.57    v1_xboole_0(sK1) | ~v1_xboole_0(sK0)),
% 1.52/0.57    inference(resolution,[],[f190,f40])).
% 1.52/0.57  fof(f190,plain,(
% 1.52/0.57    r2_hidden(sK3(sK1),sK0) | v1_xboole_0(sK1)),
% 1.52/0.57    inference(subsumption_resolution,[],[f185,f62])).
% 1.52/0.57  fof(f62,plain,(
% 1.52/0.57    ~v1_xboole_0(k1_zfmisc_1(sK0)) | v1_xboole_0(sK1)),
% 1.52/0.57    inference(resolution,[],[f35,f44])).
% 1.52/0.57  fof(f44,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f22])).
% 1.52/0.57  fof(f22,plain,(
% 1.52/0.57    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.52/0.57    inference(nnf_transformation,[],[f11])).
% 1.52/0.57  fof(f11,plain,(
% 1.52/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f6])).
% 1.52/0.57  fof(f6,axiom,(
% 1.52/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.52/0.57  fof(f35,plain,(
% 1.52/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.52/0.57    inference(cnf_transformation,[],[f17])).
% 1.52/0.57  fof(f185,plain,(
% 1.52/0.57    r2_hidden(sK3(sK1),sK0) | v1_xboole_0(k1_zfmisc_1(sK0)) | v1_xboole_0(sK1)),
% 1.52/0.57    inference(resolution,[],[f93,f41])).
% 1.52/0.57  fof(f93,plain,(
% 1.52/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 1.52/0.57    inference(resolution,[],[f83,f46])).
% 1.52/0.57  fof(f46,plain,(
% 1.52/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f26])).
% 1.52/0.57  fof(f83,plain,(
% 1.52/0.57    r1_tarski(sK1,sK0) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.52/0.57    inference(resolution,[],[f61,f60])).
% 1.52/0.57  fof(f60,plain,(
% 1.52/0.57    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.52/0.57    inference(equality_resolution,[],[f52])).
% 1.52/0.57  fof(f52,plain,(
% 1.52/0.57    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f32,plain,(
% 1.52/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 1.52/0.57  fof(f31,plain,(
% 1.52/0.57    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f30,plain,(
% 1.52/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.52/0.57    inference(rectify,[],[f29])).
% 1.52/0.57  fof(f29,plain,(
% 1.52/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.52/0.57    inference(nnf_transformation,[],[f5])).
% 1.52/0.57  fof(f5,axiom,(
% 1.52/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.52/0.57  fof(f61,plain,(
% 1.52/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.52/0.57    inference(resolution,[],[f35,f42])).
% 1.52/0.57  fof(f42,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f22])).
% 1.52/0.57  fof(f259,plain,(
% 1.52/0.57    ( ! [X2] : (r1_tarski(sK1,X2) | m1_subset_1(sK4(sK1,X2),sK0) | v1_xboole_0(sK0)) )),
% 1.52/0.57    inference(resolution,[],[f247,f43])).
% 1.52/0.57  fof(f43,plain,(
% 1.52/0.57    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f22])).
% 1.52/0.57  fof(f247,plain,(
% 1.52/0.57    ( ! [X3] : (r2_hidden(sK4(sK1,X3),sK0) | r1_tarski(sK1,X3)) )),
% 1.52/0.57    inference(resolution,[],[f243,f47])).
% 1.52/0.57  fof(f243,plain,(
% 1.52/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f242,f40])).
% 1.52/0.57  fof(f242,plain,(
% 1.52/0.57    ( ! [X0] : (r2_hidden(X0,sK0) | v1_xboole_0(sK1) | ~r2_hidden(X0,sK1)) )),
% 1.52/0.57    inference(duplicate_literal_removal,[],[f240])).
% 1.52/0.57  fof(f240,plain,(
% 1.52/0.57    ( ! [X0] : (r2_hidden(X0,sK0) | v1_xboole_0(sK1) | ~r2_hidden(X0,sK1) | v1_xboole_0(sK1)) )),
% 1.52/0.57    inference(resolution,[],[f189,f43])).
% 1.52/0.57  fof(f189,plain,(
% 1.52/0.57    ( ! [X2] : (~m1_subset_1(X2,sK1) | r2_hidden(X2,sK0) | v1_xboole_0(sK1)) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f184,f62])).
% 1.52/0.57  fof(f184,plain,(
% 1.52/0.57    ( ! [X2] : (r2_hidden(X2,sK0) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~m1_subset_1(X2,sK1) | v1_xboole_0(sK1)) )),
% 1.52/0.57    inference(resolution,[],[f93,f42])).
% 1.52/0.57  fof(f399,plain,(
% 1.52/0.57    r2_hidden(sK6(sK1,sK2),sK1) | ~r2_hidden(sK6(sK1,sK2),sK0)),
% 1.52/0.57    inference(resolution,[],[f380,f154])).
% 1.52/0.57  fof(f154,plain,(
% 1.52/0.57    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f152,f40])).
% 1.52/0.57  fof(f152,plain,(
% 1.52/0.57    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | v1_xboole_0(sK0)) )),
% 1.52/0.57    inference(resolution,[],[f38,f43])).
% 1.52/0.57  % (614)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.52/0.57  fof(f38,plain,(
% 1.52/0.57    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f17])).
% 1.52/0.57  fof(f380,plain,(
% 1.52/0.57    r2_hidden(sK6(sK1,sK2),sK2)),
% 1.52/0.57    inference(resolution,[],[f379,f56])).
% 1.52/0.57  fof(f56,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f34])).
% 1.52/0.57  fof(f791,plain,(
% 1.52/0.57    r2_hidden(sK6(sK1,sK2),sK0)),
% 1.52/0.57    inference(resolution,[],[f770,f380])).
% 1.52/0.57  fof(f770,plain,(
% 1.52/0.57    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK0)) )),
% 1.52/0.57    inference(resolution,[],[f761,f46])).
% 1.52/0.57  % (629)Refutation not found, incomplete strategy% (629)------------------------------
% 1.52/0.57  % (629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  fof(f761,plain,(
% 1.52/0.57    r1_tarski(sK2,sK0)),
% 1.52/0.57    inference(resolution,[],[f754,f60])).
% 1.52/0.57  % (629)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (634)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.52/0.57  % (629)Memory used [KB]: 1663
% 1.52/0.57  % (629)Time elapsed: 0.161 s
% 1.52/0.57  % (629)------------------------------
% 1.52/0.57  % (629)------------------------------
% 1.52/0.57  fof(f754,plain,(
% 1.52/0.57    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.52/0.57    inference(resolution,[],[f276,f36])).
% 1.52/0.57  fof(f36,plain,(
% 1.52/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.52/0.57    inference(cnf_transformation,[],[f17])).
% 1.52/0.57  fof(f276,plain,(
% 1.52/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r2_hidden(X0,k1_zfmisc_1(sK0))) )),
% 1.52/0.57    inference(resolution,[],[f273,f42])).
% 1.52/0.57  fof(f273,plain,(
% 1.52/0.57    ~v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.52/0.57    inference(resolution,[],[f267,f40])).
% 1.52/0.57  fof(f267,plain,(
% 1.52/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.52/0.57    inference(resolution,[],[f261,f59])).
% 1.52/0.57  fof(f59,plain,(
% 1.52/0.57    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.52/0.57    inference(equality_resolution,[],[f53])).
% 1.52/0.57  fof(f53,plain,(
% 1.52/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f261,plain,(
% 1.52/0.57    r1_tarski(sK1,sK0)),
% 1.52/0.57    inference(duplicate_literal_removal,[],[f257])).
% 1.52/0.57  fof(f257,plain,(
% 1.52/0.57    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 1.52/0.57    inference(resolution,[],[f247,f48])).
% 1.52/0.57  % SZS output end Proof for theBenchmark
% 1.52/0.57  % (631)------------------------------
% 1.52/0.57  % (631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (631)Termination reason: Refutation
% 1.52/0.57  
% 1.52/0.57  % (631)Memory used [KB]: 2046
% 1.52/0.57  % (631)Time elapsed: 0.133 s
% 1.52/0.57  % (631)------------------------------
% 1.52/0.57  % (631)------------------------------
% 1.52/0.57  % (606)Success in time 0.207 s
%------------------------------------------------------------------------------
