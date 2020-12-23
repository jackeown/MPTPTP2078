%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 (1056 expanded)
%              Number of leaves         :   14 ( 285 expanded)
%              Depth                    :   25
%              Number of atoms          :  254 (5149 expanded)
%              Number of equality atoms :   30 ( 516 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f545,plain,(
    $false ),
    inference(subsumption_resolution,[],[f544,f385])).

fof(f385,plain,(
    k1_xboole_0 != sK2 ),
    inference(backward_demodulation,[],[f40,f378])).

fof(f378,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f376,f231])).

fof(f231,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f215,f41])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
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

fof(f215,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f212,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f212,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(sK3(sK2),sK2) ) ),
    inference(resolution,[],[f208,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f208,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(sK2)
      | ~ r2_hidden(X6,sK1) ) ),
    inference(resolution,[],[f203,f41])).

fof(f203,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f38,f66])).

fof(f66,plain,(
    ! [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f58,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f53,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f53,plain,(
    r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f36,f51])).

% (10548)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
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

fof(f21,plain,
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

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f11])).

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
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f38,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f376,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f367,f258])).

fof(f258,plain,(
    ~ r2_hidden(sK5(sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f255,f40])).

fof(f255,plain,
    ( sK1 = sK2
    | ~ r2_hidden(sK5(sK2,sK1),sK1) ),
    inference(resolution,[],[f251,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK5(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f251,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f250,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f250,plain,(
    r1_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,
    ( r1_tarski(sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f210,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f210,plain,(
    ! [X8] :
      ( ~ r2_hidden(sK6(X8,sK2),sK1)
      | r1_tarski(X8,sK2) ) ),
    inference(resolution,[],[f203,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f367,plain,
    ( r2_hidden(sK5(sK2,sK1),sK1)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f361,f259])).

fof(f259,plain,
    ( r2_hidden(sK5(sK2,sK1),sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f257,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f257,plain,(
    m1_subset_1(sK5(sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f254,f40])).

fof(f254,plain,
    ( sK1 = sK2
    | m1_subset_1(sK5(sK2,sK1),sK2) ),
    inference(resolution,[],[f251,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK5(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f361,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f349])).

% (10570)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f349,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f39,f73])).

fof(f73,plain,(
    ! [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f64,f44])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f59,f48])).

fof(f59,plain,(
    r1_tarski(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f37,f51])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f544,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f510,f530])).

fof(f530,plain,(
    ! [X6] : ~ r2_hidden(X6,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f439,f376])).

fof(f439,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | ~ v1_xboole_0(sK2) ) ),
    inference(backward_demodulation,[],[f208,f378])).

fof(f510,plain,
    ( r2_hidden(sK4(sK2),k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f371,f378])).

fof(f371,plain,
    ( r2_hidden(sK4(sK2),sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f361,f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:03:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (10568)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (10559)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (10550)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (10555)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (10544)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (10553)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (10546)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (10545)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (10549)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (10542)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (10567)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (10572)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (10545)Refutation not found, incomplete strategy% (10545)------------------------------
% 0.21/0.53  % (10545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10545)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10545)Memory used [KB]: 10746
% 0.21/0.53  % (10545)Time elapsed: 0.118 s
% 0.21/0.53  % (10545)------------------------------
% 0.21/0.53  % (10545)------------------------------
% 0.21/0.53  % (10542)Refutation not found, incomplete strategy% (10542)------------------------------
% 0.21/0.53  % (10542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10542)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10542)Memory used [KB]: 1663
% 0.21/0.53  % (10542)Time elapsed: 0.112 s
% 0.21/0.53  % (10542)------------------------------
% 0.21/0.53  % (10542)------------------------------
% 0.21/0.53  % (10568)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f545,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f544,f385])).
% 0.21/0.53  fof(f385,plain,(
% 0.21/0.53    k1_xboole_0 != sK2),
% 0.21/0.53    inference(backward_demodulation,[],[f40,f378])).
% 0.21/0.53  fof(f378,plain,(
% 0.21/0.53    k1_xboole_0 = sK1),
% 0.21/0.53    inference(resolution,[],[f376,f231])).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    ~v1_xboole_0(sK2) | k1_xboole_0 = sK1),
% 0.21/0.53    inference(resolution,[],[f215,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.53    inference(rectify,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    r2_hidden(sK3(sK2),sK2) | k1_xboole_0 = sK1),
% 0.21/0.53    inference(resolution,[],[f212,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(sK3(sK2),sK2)) )),
% 0.21/0.53    inference(resolution,[],[f208,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    ( ! [X6] : (~v1_xboole_0(sK2) | ~r2_hidden(X6,sK1)) )),
% 0.21/0.53    inference(resolution,[],[f203,f41])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f194])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1)) )),
% 0.21/0.53    inference(resolution,[],[f38,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~r2_hidden(X2,sK1)) )),
% 0.21/0.53    inference(resolution,[],[f58,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.53    inference(resolution,[],[f53,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    r1_tarski(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(resolution,[],[f36,f51])).
% 0.21/0.53  % (10548)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.53    inference(nnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.53    inference(flattening,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.53    inference(negated_conjecture,[],[f8])).
% 0.21/0.53  fof(f8,conjecture,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f376,plain,(
% 0.21/0.53    v1_xboole_0(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f367,f258])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    ~r2_hidden(sK5(sK2,sK1),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f255,f40])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    sK1 = sK2 | ~r2_hidden(sK5(sK2,sK1),sK1)),
% 0.21/0.53    inference(resolution,[],[f251,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK5(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK2))),
% 0.21/0.53    inference(resolution,[],[f250,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    r1_tarski(sK1,sK2)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f247])).
% 0.21/0.53  fof(f247,plain,(
% 0.21/0.53    r1_tarski(sK1,sK2) | r1_tarski(sK1,sK2)),
% 0.21/0.53    inference(resolution,[],[f210,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    ( ! [X8] : (~r2_hidden(sK6(X8,sK2),sK1) | r1_tarski(X8,sK2)) )),
% 0.21/0.53    inference(resolution,[],[f203,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f367,plain,(
% 0.21/0.53    r2_hidden(sK5(sK2,sK1),sK1) | v1_xboole_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f361,f259])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    r2_hidden(sK5(sK2,sK1),sK2) | v1_xboole_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f257,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    m1_subset_1(sK5(sK2,sK1),sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f254,f40])).
% 0.21/0.54  fof(f254,plain,(
% 0.21/0.54    sK1 = sK2 | m1_subset_1(sK5(sK2,sK1),sK2)),
% 0.21/0.54    inference(resolution,[],[f251,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK5(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f361,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f349])).
% 0.21/0.54  % (10570)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  fof(f349,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.54    inference(resolution,[],[f39,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~r2_hidden(X2,sK2)) )),
% 0.21/0.54    inference(resolution,[],[f64,f44])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.54    inference(resolution,[],[f59,f48])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    r1_tarski(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(resolution,[],[f37,f51])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    sK1 != sK2),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f544,plain,(
% 0.21/0.54    k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f510,f530])).
% 0.21/0.54  fof(f530,plain,(
% 0.21/0.54    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f439,f376])).
% 0.21/0.54  fof(f439,plain,(
% 0.21/0.54    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0) | ~v1_xboole_0(sK2)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f208,f378])).
% 0.21/0.54  fof(f510,plain,(
% 0.21/0.54    r2_hidden(sK4(sK2),k1_xboole_0) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(backward_demodulation,[],[f371,f378])).
% 0.21/0.54  fof(f371,plain,(
% 0.21/0.54    r2_hidden(sK4(sK2),sK1) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(resolution,[],[f361,f43])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (10568)------------------------------
% 0.21/0.54  % (10568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10568)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (10568)Memory used [KB]: 1918
% 0.21/0.54  % (10568)Time elapsed: 0.069 s
% 0.21/0.54  % (10568)------------------------------
% 0.21/0.54  % (10568)------------------------------
% 0.21/0.54  % (10537)Success in time 0.174 s
%------------------------------------------------------------------------------
