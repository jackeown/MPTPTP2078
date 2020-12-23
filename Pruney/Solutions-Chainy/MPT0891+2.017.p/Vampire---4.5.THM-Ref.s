%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 256 expanded)
%              Number of leaves         :   14 (  81 expanded)
%              Depth                    :   21
%              Number of atoms          :  287 (1345 expanded)
%              Number of equality atoms :  201 ( 975 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f412,plain,(
    $false ),
    inference(subsumption_resolution,[],[f393,f67])).

fof(f67,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f41,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f393,plain,(
    r2_hidden(sK3,k1_xboole_0) ),
    inference(superposition,[],[f63,f385])).

fof(f385,plain,(
    k1_xboole_0 = k1_tarski(sK3) ),
    inference(trivial_inequality_removal,[],[f384])).

fof(f384,plain,
    ( sK3 != sK3
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(duplicate_literal_removal,[],[f381])).

fof(f381,plain,
    ( sK3 != sK3
    | k1_xboole_0 = k1_tarski(sK3)
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(superposition,[],[f184,f372])).

fof(f372,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(subsumption_resolution,[],[f371,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f83,f63])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | k4_tarski(X1,X2) != X0
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | ~ r2_hidden(X2,k1_tarski(X0))
      | k1_tarski(X0) = k1_xboole_0
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(superposition,[],[f37,f72])).

fof(f72,plain,(
    ! [X1] :
      ( sK4(k1_tarski(X1)) = X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f64,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

% (22523)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f64,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).

% (22518)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f371,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3) ),
    inference(trivial_inequality_removal,[],[f369])).

% (22523)Refutation not found, incomplete strategy% (22523)------------------------------
% (22523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22523)Termination reason: Refutation not found, incomplete strategy

% (22523)Memory used [KB]: 6268
% (22523)Time elapsed: 0.140 s
% (22523)------------------------------
% (22523)------------------------------
fof(f369,plain,
    ( sK3 != sK3
    | k1_xboole_0 = k1_tarski(sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3) ),
    inference(superposition,[],[f328,f152])).

fof(f152,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3) ),
    inference(superposition,[],[f149,f34])).

fof(f34,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f18,f17])).

fof(f17,plain,
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

fof(f18,plain,
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

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f149,plain,(
    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f148,f30])).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f148,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f147,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f147,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f143,f32])).

fof(f32,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f143,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f58,f55])).

fof(f55,plain,(
    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f33,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f328,plain,
    ( sK3 != k5_mcart_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = k1_tarski(k5_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(resolution,[],[f179,f63])).

fof(f179,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),k1_tarski(X0))
      | sK3 != X0
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
    ! [X0] :
      ( sK3 != X0
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),k1_tarski(X0))
      | k1_tarski(X0) = k1_xboole_0
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(superposition,[],[f162,f73])).

fof(f73,plain,(
    ! [X2] :
      ( sK5(k1_tarski(X2)) = X2
      | k1_xboole_0 = k1_tarski(X2) ) ),
    inference(resolution,[],[f64,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f162,plain,(
    ! [X9] :
      ( sK3 != sK5(X9)
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),X9)
      | k1_xboole_0 = X9 ) ),
    inference(superposition,[],[f57,f149])).

fof(f57,plain,(
    ! [X4,X2,X0,X3] :
      ( sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f39,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK5(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f184,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = k1_tarski(k6_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(resolution,[],[f161,f63])).

fof(f161,plain,(
    ! [X8] :
      ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK3),k1_tarski(X8))
      | sK3 != X8
      | k1_xboole_0 = k1_tarski(X8) ) ),
    inference(superposition,[],[f105,f149])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X2,k1_tarski(X0))
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(duplicate_literal_removal,[],[f104])).

% (22513)Termination reason: Refutation not found, incomplete strategy

% (22513)Memory used [KB]: 10618
% (22513)Time elapsed: 0.140 s
% (22513)------------------------------
% (22513)------------------------------
fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X2,k1_tarski(X0))
      | k1_tarski(X0) = k1_xboole_0
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(superposition,[],[f56,f73])).

fof(f56,plain,(
    ! [X4,X2,X0,X3] :
      ( sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f40,f49])).

fof(f40,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK5(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (22519)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (22507)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (22504)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (22508)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (22501)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (22506)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (22503)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (22502)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (22521)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (22498)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (22526)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (22521)Refutation not found, incomplete strategy% (22521)------------------------------
% 0.20/0.54  % (22521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22521)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22521)Memory used [KB]: 10746
% 0.20/0.54  % (22521)Time elapsed: 0.130 s
% 0.20/0.54  % (22521)------------------------------
% 0.20/0.54  % (22521)------------------------------
% 0.20/0.54  % (22498)Refutation not found, incomplete strategy% (22498)------------------------------
% 0.20/0.54  % (22498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22498)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22498)Memory used [KB]: 1663
% 0.20/0.54  % (22498)Time elapsed: 0.122 s
% 0.20/0.54  % (22498)------------------------------
% 0.20/0.54  % (22498)------------------------------
% 0.20/0.54  % (22526)Refutation not found, incomplete strategy% (22526)------------------------------
% 0.20/0.54  % (22526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22526)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22526)Memory used [KB]: 1663
% 0.20/0.54  % (22526)Time elapsed: 0.127 s
% 0.20/0.54  % (22526)------------------------------
% 0.20/0.54  % (22526)------------------------------
% 0.20/0.54  % (22500)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (22511)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (22496)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (22511)Refutation not found, incomplete strategy% (22511)------------------------------
% 0.20/0.54  % (22511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22511)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22511)Memory used [KB]: 1791
% 0.20/0.54  % (22511)Time elapsed: 0.127 s
% 0.20/0.54  % (22511)------------------------------
% 0.20/0.54  % (22511)------------------------------
% 0.20/0.54  % (22509)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (22524)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (22513)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (22509)Refutation not found, incomplete strategy% (22509)------------------------------
% 0.20/0.54  % (22509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22509)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22509)Memory used [KB]: 10618
% 0.20/0.54  % (22509)Time elapsed: 0.138 s
% 0.20/0.54  % (22509)------------------------------
% 0.20/0.54  % (22509)------------------------------
% 0.20/0.54  % (22499)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (22517)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (22513)Refutation not found, incomplete strategy% (22513)------------------------------
% 0.20/0.54  % (22513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22519)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f412,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f393,f67])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(superposition,[],[f41,f65])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.55    inference(flattening,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.55    inference(nnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.55  fof(f393,plain,(
% 0.20/0.55    r2_hidden(sK3,k1_xboole_0)),
% 0.20/0.55    inference(superposition,[],[f63,f385])).
% 0.20/0.55  fof(f385,plain,(
% 0.20/0.55    k1_xboole_0 = k1_tarski(sK3)),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f384])).
% 0.20/0.55  fof(f384,plain,(
% 0.20/0.55    sK3 != sK3 | k1_xboole_0 = k1_tarski(sK3)),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f381])).
% 0.20/0.55  fof(f381,plain,(
% 0.20/0.55    sK3 != sK3 | k1_xboole_0 = k1_tarski(sK3) | k1_xboole_0 = k1_tarski(sK3)),
% 0.20/0.55    inference(superposition,[],[f184,f372])).
% 0.20/0.55  fof(f372,plain,(
% 0.20/0.55    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = k1_tarski(sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f371,f99])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_tarski(X0,X1) != X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 0.20/0.55    inference(resolution,[],[f83,f63])).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_tarski(X0)) | k4_tarski(X1,X2) != X0 | k1_tarski(X0) = k1_xboole_0) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | ~r2_hidden(X2,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0 | k1_tarski(X0) = k1_xboole_0) )),
% 0.20/0.55    inference(superposition,[],[f37,f72])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X1] : (sK4(k1_tarski(X1)) = X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 0.20/0.55    inference(resolution,[],[f64,f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.20/0.55  % (22523)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.55    inference(equality_resolution,[],[f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).
% 0.20/0.55  % (22518)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(rectify,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK4(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f371,plain,(
% 0.20/0.55    k1_xboole_0 = k1_tarski(sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f369])).
% 0.20/0.55  % (22523)Refutation not found, incomplete strategy% (22523)------------------------------
% 0.20/0.55  % (22523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22523)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (22523)Memory used [KB]: 6268
% 0.20/0.55  % (22523)Time elapsed: 0.140 s
% 0.20/0.55  % (22523)------------------------------
% 0.20/0.55  % (22523)------------------------------
% 0.20/0.55  fof(f369,plain,(
% 0.20/0.55    sK3 != sK3 | k1_xboole_0 = k1_tarski(sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)),
% 0.20/0.55    inference(superposition,[],[f328,f152])).
% 0.20/0.55  fof(f152,plain,(
% 0.20/0.55    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)),
% 0.20/0.55    inference(superposition,[],[f149,f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f18,f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) => ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.55    inference(negated_conjecture,[],[f10])).
% 0.20/0.55  fof(f10,conjecture,(
% 0.20/0.55    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).
% 0.20/0.55  fof(f149,plain,(
% 0.20/0.55    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 0.20/0.55    inference(subsumption_resolution,[],[f148,f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    k1_xboole_0 != sK0),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f148,plain,(
% 0.20/0.55    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.20/0.55    inference(subsumption_resolution,[],[f147,f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    k1_xboole_0 != sK1),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f147,plain,(
% 0.20/0.55    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.55    inference(subsumption_resolution,[],[f143,f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    k1_xboole_0 != sK2),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f143,plain,(
% 0.20/0.55    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.55    inference(resolution,[],[f58,f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.55    inference(definition_unfolding,[],[f33,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(definition_unfolding,[],[f51,f49,f50])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 0.20/0.55  fof(f328,plain,(
% 0.20/0.55    sK3 != k5_mcart_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = k1_tarski(k5_mcart_1(sK0,sK1,sK2,sK3))),
% 0.20/0.55    inference(resolution,[],[f179,f63])).
% 0.20/0.55  fof(f179,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),k1_tarski(X0)) | sK3 != X0 | k1_tarski(X0) = k1_xboole_0) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f178])).
% 0.20/0.55  fof(f178,plain,(
% 0.20/0.55    ( ! [X0] : (sK3 != X0 | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0 | k1_tarski(X0) = k1_xboole_0) )),
% 0.20/0.55    inference(superposition,[],[f162,f73])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X2] : (sK5(k1_tarski(X2)) = X2 | k1_xboole_0 = k1_tarski(X2)) )),
% 0.20/0.55    inference(resolution,[],[f64,f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.20/0.55  fof(f162,plain,(
% 0.20/0.55    ( ! [X9] : (sK3 != sK5(X9) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),X9) | k1_xboole_0 = X9) )),
% 0.20/0.55    inference(superposition,[],[f57,f149])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3] : (sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(definition_unfolding,[],[f39,f49])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f184,plain,(
% 0.20/0.55    sK3 != k6_mcart_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = k1_tarski(k6_mcart_1(sK0,sK1,sK2,sK3))),
% 0.20/0.55    inference(resolution,[],[f161,f63])).
% 0.20/0.55  fof(f161,plain,(
% 0.20/0.55    ( ! [X8] : (~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK3),k1_tarski(X8)) | sK3 != X8 | k1_xboole_0 = k1_tarski(X8)) )),
% 0.20/0.55    inference(superposition,[],[f105,f149])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X2,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f104])).
% 0.20/0.55  % (22513)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (22513)Memory used [KB]: 10618
% 0.20/0.55  % (22513)Time elapsed: 0.140 s
% 0.20/0.55  % (22513)------------------------------
% 0.20/0.55  % (22513)------------------------------
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X2,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0 | k1_tarski(X0) = k1_xboole_0) )),
% 0.20/0.55    inference(superposition,[],[f56,f73])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3] : (sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(definition_unfolding,[],[f40,f49])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.20/0.55    inference(equality_resolution,[],[f62])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.20/0.55    inference(equality_resolution,[],[f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (22519)------------------------------
% 0.20/0.55  % (22519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22519)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (22505)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (22519)Memory used [KB]: 6524
% 0.20/0.55  % (22519)Time elapsed: 0.035 s
% 0.20/0.55  % (22519)------------------------------
% 0.20/0.55  % (22519)------------------------------
% 0.20/0.55  % (22515)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (22516)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (22525)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (22515)Refutation not found, incomplete strategy% (22515)------------------------------
% 0.20/0.55  % (22515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22515)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (22515)Memory used [KB]: 1663
% 0.20/0.55  % (22515)Time elapsed: 0.150 s
% 0.20/0.55  % (22515)------------------------------
% 0.20/0.55  % (22515)------------------------------
% 0.20/0.55  % (22494)Success in time 0.192 s
%------------------------------------------------------------------------------
