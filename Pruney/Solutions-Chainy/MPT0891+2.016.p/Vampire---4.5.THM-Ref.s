%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 568 expanded)
%              Number of leaves         :   15 ( 193 expanded)
%              Depth                    :   30
%              Number of atoms          :  398 (3039 expanded)
%              Number of equality atoms :  319 (2449 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (18873)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f326,plain,(
    $false ),
    inference(subsumption_resolution,[],[f325,f71])).

fof(f71,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f39,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f325,plain,(
    r2_hidden(sK3,k1_xboole_0) ),
    inference(superposition,[],[f65,f320])).

fof(f320,plain,(
    k1_xboole_0 = k1_tarski(sK3) ),
    inference(subsumption_resolution,[],[f319,f75])).

fof(f75,plain,(
    ! [X1] :
      ( sK4(k1_tarski(X1)) = X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f66,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f66,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f319,plain,
    ( sK3 != sK4(k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(resolution,[],[f310,f65])).

fof(f310,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | sK3 != sK4(X0)
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f236,f307])).

fof(f307,plain,(
    sK3 = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f306,f71])).

fof(f306,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | sK3 = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f65,f301])).

fof(f301,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | sK3 = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f300])).

fof(f300,plain,
    ( sK3 != sK3
    | k1_xboole_0 = k1_tarski(sK3)
    | sK3 = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f256,f169])).

fof(f169,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | sK3 = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f168])).

fof(f168,plain,
    ( sK3 != sK3
    | sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f167,f108])).

fof(f108,plain,
    ( sK3 = k2_mcart_1(sK3)
    | sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f107,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK0,sK1,sK2,X3) = X3
            | k6_mcart_1(sK0,sK1,sK2,X3) = X3
            | k5_mcart_1(sK0,sK1,sK2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK0,sK1,sK2,X3) = X3
          | k6_mcart_1(sK0,sK1,sK2,X3) = X3
          | k5_mcart_1(sK0,sK1,sK2,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
        | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
        | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
      & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f107,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f106,f30])).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f106,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f105,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f105,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f103,f55])).

fof(f55,plain,(
    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f32,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f32,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f61,f102])).

fof(f102,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f101,f29])).

fof(f101,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f100,f30])).

fof(f100,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f99,f31])).

fof(f99,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f97,f55])).

fof(f97,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f60,f94])).

fof(f94,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f93,f29])).

fof(f93,plain,
    ( sK3 = k2_mcart_1(sK3)
    | k1_xboole_0 = sK0
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f92,f30])).

fof(f92,plain,
    ( sK3 = k2_mcart_1(sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f91,f31])).

fof(f91,plain,
    ( sK3 = k2_mcart_1(sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f89,f55])).

fof(f89,plain,
    ( sK3 = k2_mcart_1(sK3)
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f59,f33])).

fof(f33,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f54,f50])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f53,f50])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f50])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f167,plain,(
    sK3 != k2_mcart_1(sK3) ),
    inference(subsumption_resolution,[],[f166,f29])).

fof(f166,plain,
    ( sK3 != k2_mcart_1(sK3)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f165,f30])).

fof(f165,plain,
    ( sK3 != k2_mcart_1(sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f164,f31])).

fof(f164,plain,
    ( sK3 != k2_mcart_1(sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f162,f55])).

fof(f162,plain,
    ( sK3 != k2_mcart_1(sK3)
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f134,f59])).

fof(f134,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f69,f120])).

fof(f120,plain,(
    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f119,f29])).

fof(f119,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f118,f30])).

fof(f118,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f114,f31])).

fof(f114,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f58,f55])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f49,f50])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

% (18855)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f69,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(backward_demodulation,[],[f62,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f62,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f256,plain,
    ( sK3 != k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = k1_tarski(k2_mcart_1(k1_mcart_1(sK3))) ),
    inference(forward_demodulation,[],[f249,f216])).

fof(f216,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f41,f130])).

fof(f130,plain,(
    k1_mcart_1(sK3) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(superposition,[],[f40,f120])).

fof(f40,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f249,plain,
    ( sK3 != k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = k1_tarski(k6_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(backward_demodulation,[],[f127,f216])).

fof(f127,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = k1_tarski(k6_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(superposition,[],[f109,f120])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k4_tarski(X0,X1),X2) != X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f86,f65])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | k4_tarski(k4_tarski(X1,X2),X3) != X0
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X2,k1_tarski(X0))
      | k1_tarski(X0) = k1_xboole_0
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(superposition,[],[f56,f75])).

fof(f56,plain,(
    ! [X4,X2,X0,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f38,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f236,plain,(
    ! [X0] :
      ( sK3 != sK4(X0)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f128,f215])).

fof(f215,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f40,f130])).

fof(f128,plain,(
    ! [X0] :
      ( sK3 != sK4(X0)
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f57,f120])).

fof(f57,plain,(
    ! [X4,X2,X0,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f37,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK4(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

% (18865)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:28:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.53  % (18862)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (18870)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (18870)Refutation not found, incomplete strategy% (18870)------------------------------
% 0.21/0.53  % (18870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18878)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (18870)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18870)Memory used [KB]: 10618
% 0.21/0.54  % (18870)Time elapsed: 0.116 s
% 0.21/0.54  % (18870)------------------------------
% 0.21/0.54  % (18870)------------------------------
% 0.21/0.56  % (18876)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (18878)Refutation not found, incomplete strategy% (18878)------------------------------
% 0.21/0.56  % (18878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18878)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18878)Memory used [KB]: 10746
% 0.21/0.56  % (18878)Time elapsed: 0.140 s
% 0.21/0.56  % (18878)------------------------------
% 0.21/0.56  % (18878)------------------------------
% 0.21/0.57  % (18860)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (18868)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (18868)Refutation not found, incomplete strategy% (18868)------------------------------
% 0.21/0.57  % (18868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (18881)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.59  % (18856)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.59  % (18868)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (18868)Memory used [KB]: 1791
% 0.21/0.59  % (18868)Time elapsed: 0.092 s
% 0.21/0.59  % (18868)------------------------------
% 0.21/0.59  % (18868)------------------------------
% 0.21/0.59  % (18857)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.59  % (18858)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.59  % (18859)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.59  % (18854)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.59  % (18876)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % (18861)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  % (18873)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.59  fof(f326,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(subsumption_resolution,[],[f325,f71])).
% 0.21/0.59  fof(f71,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.59    inference(superposition,[],[f39,f67])).
% 0.21/0.60  fof(f67,plain,(
% 0.21/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.60    inference(equality_resolution,[],[f48])).
% 0.21/0.60  fof(f48,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f28])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.60    inference(flattening,[],[f27])).
% 0.21/0.60  fof(f27,plain,(
% 0.21/0.60    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.60    inference(nnf_transformation,[],[f2])).
% 0.21/0.60  fof(f2,axiom,(
% 0.21/0.60    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.60  fof(f39,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f3])).
% 0.21/0.60  fof(f3,axiom,(
% 0.21/0.60    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.60  fof(f325,plain,(
% 0.21/0.60    r2_hidden(sK3,k1_xboole_0)),
% 0.21/0.60    inference(superposition,[],[f65,f320])).
% 0.21/0.60  fof(f320,plain,(
% 0.21/0.60    k1_xboole_0 = k1_tarski(sK3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f319,f75])).
% 0.21/0.60  fof(f75,plain,(
% 0.21/0.60    ( ! [X1] : (sK4(k1_tarski(X1)) = X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 0.21/0.60    inference(resolution,[],[f66,f36])).
% 0.21/0.60  fof(f36,plain,(
% 0.21/0.60    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f22])).
% 0.21/0.60  fof(f22,plain,(
% 0.21/0.60    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f21])).
% 0.21/0.60  fof(f21,plain,(
% 0.21/0.60    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f15,plain,(
% 0.21/0.60    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.60    inference(ennf_transformation,[],[f7])).
% 0.21/0.60  fof(f7,axiom,(
% 0.21/0.60    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.60  fof(f66,plain,(
% 0.21/0.60    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.60    inference(equality_resolution,[],[f42])).
% 0.21/0.60  fof(f42,plain,(
% 0.21/0.60    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f26])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).
% 0.21/0.60  fof(f25,plain,(
% 0.21/0.60    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.60    inference(rectify,[],[f23])).
% 0.21/0.60  fof(f23,plain,(
% 0.21/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.60    inference(nnf_transformation,[],[f1])).
% 0.21/0.60  fof(f1,axiom,(
% 0.21/0.60    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.60  fof(f319,plain,(
% 0.21/0.60    sK3 != sK4(k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(sK3)),
% 0.21/0.60    inference(resolution,[],[f310,f65])).
% 0.21/0.60  fof(f310,plain,(
% 0.21/0.60    ( ! [X0] : (~r2_hidden(sK3,X0) | sK3 != sK4(X0) | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(backward_demodulation,[],[f236,f307])).
% 0.21/0.60  fof(f307,plain,(
% 0.21/0.60    sK3 = k1_mcart_1(k1_mcart_1(sK3))),
% 0.21/0.60    inference(subsumption_resolution,[],[f306,f71])).
% 0.21/0.60  fof(f306,plain,(
% 0.21/0.60    r2_hidden(sK3,k1_xboole_0) | sK3 = k1_mcart_1(k1_mcart_1(sK3))),
% 0.21/0.60    inference(superposition,[],[f65,f301])).
% 0.21/0.60  fof(f301,plain,(
% 0.21/0.60    k1_xboole_0 = k1_tarski(sK3) | sK3 = k1_mcart_1(k1_mcart_1(sK3))),
% 0.21/0.60    inference(trivial_inequality_removal,[],[f300])).
% 0.21/0.60  fof(f300,plain,(
% 0.21/0.60    sK3 != sK3 | k1_xboole_0 = k1_tarski(sK3) | sK3 = k1_mcart_1(k1_mcart_1(sK3))),
% 0.21/0.60    inference(superposition,[],[f256,f169])).
% 0.21/0.60  fof(f169,plain,(
% 0.21/0.60    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | sK3 = k1_mcart_1(k1_mcart_1(sK3))),
% 0.21/0.60    inference(trivial_inequality_removal,[],[f168])).
% 0.21/0.60  fof(f168,plain,(
% 0.21/0.60    sK3 != sK3 | sK3 = k1_mcart_1(k1_mcart_1(sK3)) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 0.21/0.60    inference(superposition,[],[f167,f108])).
% 0.21/0.60  fof(f108,plain,(
% 0.21/0.60    sK3 = k2_mcart_1(sK3) | sK3 = k1_mcart_1(k1_mcart_1(sK3)) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 0.21/0.60    inference(subsumption_resolution,[],[f107,f29])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    k1_xboole_0 != sK0),
% 0.21/0.60    inference(cnf_transformation,[],[f20])).
% 0.21/0.60  fof(f20,plain,(
% 0.21/0.60    ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f19,f18])).
% 0.21/0.60  fof(f18,plain,(
% 0.21/0.60    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f19,plain,(
% 0.21/0.60    ? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) => ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f13,plain,(
% 0.21/0.60    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.60    inference(ennf_transformation,[],[f12])).
% 0.21/0.60  fof(f12,negated_conjecture,(
% 0.21/0.60    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.60    inference(negated_conjecture,[],[f11])).
% 0.21/0.60  fof(f11,conjecture,(
% 0.21/0.60    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).
% 0.21/0.60  fof(f107,plain,(
% 0.21/0.60    sK3 = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 0.21/0.60    inference(subsumption_resolution,[],[f106,f30])).
% 0.21/0.60  fof(f30,plain,(
% 0.21/0.60    k1_xboole_0 != sK1),
% 0.21/0.60    inference(cnf_transformation,[],[f20])).
% 0.21/0.60  fof(f106,plain,(
% 0.21/0.60    sK3 = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 0.21/0.60    inference(subsumption_resolution,[],[f105,f31])).
% 0.21/0.60  fof(f31,plain,(
% 0.21/0.60    k1_xboole_0 != sK2),
% 0.21/0.60    inference(cnf_transformation,[],[f20])).
% 0.21/0.60  fof(f105,plain,(
% 0.21/0.60    sK3 = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 0.21/0.60    inference(subsumption_resolution,[],[f103,f55])).
% 0.21/0.60  fof(f55,plain,(
% 0.21/0.60    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.60    inference(definition_unfolding,[],[f32,f50])).
% 0.21/0.60  fof(f50,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f5])).
% 0.21/0.60  fof(f5,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.60    inference(cnf_transformation,[],[f20])).
% 0.21/0.60  fof(f103,plain,(
% 0.21/0.60    sK3 = k1_mcart_1(k1_mcart_1(sK3)) | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 0.21/0.60    inference(superposition,[],[f61,f102])).
% 0.21/0.60  fof(f102,plain,(
% 0.21/0.60    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k2_mcart_1(sK3) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 0.21/0.60    inference(subsumption_resolution,[],[f101,f29])).
% 0.21/0.60  fof(f101,plain,(
% 0.21/0.60    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f100,f30])).
% 0.21/0.60  fof(f100,plain,(
% 0.21/0.60    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f99,f31])).
% 0.21/0.60  fof(f99,plain,(
% 0.21/0.60    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f97,f55])).
% 0.21/0.60  fof(f97,plain,(
% 0.21/0.60    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.60    inference(superposition,[],[f60,f94])).
% 0.21/0.60  fof(f94,plain,(
% 0.21/0.60    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k2_mcart_1(sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f93,f29])).
% 0.21/0.60  fof(f93,plain,(
% 0.21/0.60    sK3 = k2_mcart_1(sK3) | k1_xboole_0 = sK0 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f92,f30])).
% 0.21/0.60  fof(f92,plain,(
% 0.21/0.60    sK3 = k2_mcart_1(sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f91,f31])).
% 0.21/0.60  fof(f91,plain,(
% 0.21/0.60    sK3 = k2_mcart_1(sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f89,f55])).
% 0.21/0.60  fof(f89,plain,(
% 0.21/0.60    sK3 = k2_mcart_1(sK3) | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.60    inference(superposition,[],[f59,f33])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.60    inference(cnf_transformation,[],[f20])).
% 0.21/0.60  fof(f59,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(definition_unfolding,[],[f54,f50])).
% 0.21/0.60  fof(f54,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f17])).
% 0.21/0.60  fof(f17,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.60    inference(ennf_transformation,[],[f9])).
% 0.21/0.60  fof(f9,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.60  fof(f60,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(definition_unfolding,[],[f53,f50])).
% 0.21/0.60  fof(f53,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f17])).
% 0.21/0.60  fof(f61,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(definition_unfolding,[],[f52,f50])).
% 0.21/0.60  fof(f52,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f17])).
% 0.21/0.60  fof(f167,plain,(
% 0.21/0.60    sK3 != k2_mcart_1(sK3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f166,f29])).
% 0.21/0.60  fof(f166,plain,(
% 0.21/0.60    sK3 != k2_mcart_1(sK3) | k1_xboole_0 = sK0),
% 0.21/0.60    inference(subsumption_resolution,[],[f165,f30])).
% 0.21/0.60  fof(f165,plain,(
% 0.21/0.60    sK3 != k2_mcart_1(sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.60    inference(subsumption_resolution,[],[f164,f31])).
% 0.21/0.60  fof(f164,plain,(
% 0.21/0.60    sK3 != k2_mcart_1(sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.60    inference(subsumption_resolution,[],[f162,f55])).
% 0.21/0.60  fof(f162,plain,(
% 0.21/0.60    sK3 != k2_mcart_1(sK3) | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.60    inference(superposition,[],[f134,f59])).
% 0.21/0.60  fof(f134,plain,(
% 0.21/0.60    sK3 != k7_mcart_1(sK0,sK1,sK2,sK3)),
% 0.21/0.60    inference(superposition,[],[f69,f120])).
% 0.21/0.60  fof(f120,plain,(
% 0.21/0.60    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 0.21/0.60    inference(subsumption_resolution,[],[f119,f29])).
% 0.21/0.60  fof(f119,plain,(
% 0.21/0.60    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.21/0.60    inference(subsumption_resolution,[],[f118,f30])).
% 0.21/0.60  fof(f118,plain,(
% 0.21/0.60    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.60    inference(subsumption_resolution,[],[f114,f31])).
% 0.21/0.60  fof(f114,plain,(
% 0.21/0.60    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.60    inference(resolution,[],[f58,f55])).
% 0.21/0.60  fof(f58,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(definition_unfolding,[],[f51,f49,f50])).
% 0.21/0.60  fof(f49,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.60  fof(f51,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f16])).
% 0.21/0.60  fof(f16,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.60    inference(ennf_transformation,[],[f8])).
% 0.21/0.60  % (18855)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.60  fof(f8,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 0.21/0.60  fof(f69,plain,(
% 0.21/0.60    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 0.21/0.60    inference(backward_demodulation,[],[f62,f41])).
% 0.21/0.60  fof(f41,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f10])).
% 0.21/0.60  fof(f10,axiom,(
% 0.21/0.60    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.60  fof(f62,plain,(
% 0.21/0.60    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.60    inference(equality_resolution,[],[f35])).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f14])).
% 0.21/0.60  fof(f14,plain,(
% 0.21/0.60    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.60    inference(ennf_transformation,[],[f6])).
% 0.21/0.60  fof(f6,axiom,(
% 0.21/0.60    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.60  fof(f256,plain,(
% 0.21/0.60    sK3 != k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = k1_tarski(k2_mcart_1(k1_mcart_1(sK3)))),
% 0.21/0.60    inference(forward_demodulation,[],[f249,f216])).
% 0.21/0.60  fof(f216,plain,(
% 0.21/0.60    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))),
% 0.21/0.60    inference(superposition,[],[f41,f130])).
% 0.21/0.60  fof(f130,plain,(
% 0.21/0.60    k1_mcart_1(sK3) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3))),
% 0.21/0.60    inference(superposition,[],[f40,f120])).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f10])).
% 0.21/0.60  fof(f249,plain,(
% 0.21/0.60    sK3 != k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = k1_tarski(k6_mcart_1(sK0,sK1,sK2,sK3))),
% 0.21/0.60    inference(backward_demodulation,[],[f127,f216])).
% 0.21/0.60  fof(f127,plain,(
% 0.21/0.60    sK3 != k6_mcart_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = k1_tarski(k6_mcart_1(sK0,sK1,sK2,sK3))),
% 0.21/0.60    inference(superposition,[],[f109,f120])).
% 0.21/0.60  fof(f109,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) != X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 0.21/0.60    inference(resolution,[],[f86,f65])).
% 0.21/0.60  fof(f86,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,k1_tarski(X0)) | k4_tarski(k4_tarski(X1,X2),X3) != X0 | k1_tarski(X0) = k1_xboole_0) )),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f85])).
% 0.21/0.60  fof(f85,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X2,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0 | k1_tarski(X0) = k1_xboole_0) )),
% 0.21/0.60    inference(superposition,[],[f56,f75])).
% 0.21/0.60  fof(f56,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X3] : (sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(definition_unfolding,[],[f38,f49])).
% 0.21/0.60  fof(f38,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f22])).
% 0.21/0.60  fof(f236,plain,(
% 0.21/0.60    ( ! [X0] : (sK3 != sK4(X0) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),X0) | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(backward_demodulation,[],[f128,f215])).
% 0.21/0.60  fof(f215,plain,(
% 0.21/0.60    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))),
% 0.21/0.60    inference(superposition,[],[f40,f130])).
% 0.21/0.60  fof(f128,plain,(
% 0.21/0.60    ( ! [X0] : (sK3 != sK4(X0) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),X0) | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(superposition,[],[f57,f120])).
% 0.21/0.60  fof(f57,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X3] : (sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(definition_unfolding,[],[f37,f49])).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f22])).
% 0.21/0.60  fof(f65,plain,(
% 0.21/0.60    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.60    inference(equality_resolution,[],[f64])).
% 0.21/0.60  fof(f64,plain,(
% 0.21/0.60    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.60    inference(equality_resolution,[],[f43])).
% 0.21/0.60  fof(f43,plain,(
% 0.21/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f26])).
% 0.21/0.60  % (18865)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.60  % SZS output end Proof for theBenchmark
% 0.21/0.60  % (18876)------------------------------
% 0.21/0.60  % (18876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (18876)Termination reason: Refutation
% 0.21/0.60  
% 0.21/0.60  % (18876)Memory used [KB]: 6396
% 0.21/0.60  % (18876)Time elapsed: 0.110 s
% 0.21/0.60  % (18876)------------------------------
% 0.21/0.60  % (18876)------------------------------
% 1.91/0.61  % (18853)Success in time 0.249 s
%------------------------------------------------------------------------------
