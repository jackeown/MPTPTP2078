%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:49 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 680 expanded)
%              Number of leaves         :   18 ( 191 expanded)
%              Depth                    :   16
%              Number of atoms          :  388 (2206 expanded)
%              Number of equality atoms :  173 ( 579 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(subsumption_resolution,[],[f192,f43])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f192,plain,(
    k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f144,f175])).

% (26420)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f175,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f124,f126,f135,f143,f148,f152,f164,f174])).

fof(f174,plain,
    ( ~ r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4)
    | ~ r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3)
    | ~ r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2)
    | ~ r2_hidden(sK6(sK1,sK2,sK3,sK4,sK0),sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f173,f164])).

fof(f173,plain,
    ( ~ r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4)
    | ~ r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3)
    | ~ r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2)
    | ~ r2_hidden(sK6(sK1,sK2,sK3,sK4,sK0),sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f172,f148])).

fof(f172,plain,
    ( ~ r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4)
    | ~ r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3)
    | ~ r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2)
    | ~ r2_hidden(sK6(sK1,sK2,sK3,sK4,sK0),sK1)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f168,f98])).

fof(f98,plain,(
    k1_xboole_0 != sK4 ),
    inference(superposition,[],[f94,f43])).

fof(f94,plain,(
    k1_xboole_0 != k3_xboole_0(sK4,sK4) ),
    inference(unit_resulting_resolution,[],[f86,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f86,plain,(
    ~ r1_xboole_0(sK4,sK4) ),
    inference(unit_resulting_resolution,[],[f72,f79,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f79,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(unit_resulting_resolution,[],[f74,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f74,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(unit_resulting_resolution,[],[f66,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f66,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f41,plain,(
    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ! [X5,X6,X7,X8] :
        ( k4_mcart_1(X5,X6,X7,X8) != sK0
        | ~ r2_hidden(X8,sK4)
        | ~ r2_hidden(X7,sK3)
        | ~ r2_hidden(X6,sK2)
        | ~ r2_hidden(X5,sK1) )
    & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ! [X5,X6,X7,X8] :
            ( k4_mcart_1(X5,X6,X7,X8) != X0
            | ~ r2_hidden(X8,X4)
            | ~ r2_hidden(X7,X3)
            | ~ r2_hidden(X6,X2)
            | ~ r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) )
   => ( ! [X8,X7,X6,X5] :
          ( k4_mcart_1(X5,X6,X7,X8) != sK0
          | ~ r2_hidden(X8,sK4)
          | ~ r2_hidden(X7,sK3)
          | ~ r2_hidden(X6,sK2)
          | ~ r2_hidden(X5,sK1) )
      & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( k4_mcart_1(X5,X6,X7,X8) != X0
          | ~ r2_hidden(X8,X4)
          | ~ r2_hidden(X7,X3)
          | ~ r2_hidden(X6,X2)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6,X7,X8] :
              ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
                & r2_hidden(X8,X4)
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) )
          & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6,X7,X8] :
            ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
              & r2_hidden(X8,X4)
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f168,plain,
    ( ~ r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4)
    | ~ r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3)
    | ~ r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2)
    | ~ r2_hidden(sK6(sK1,sK2,sK3,sK4,sK0),sK1)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f166])).

fof(f166,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4)
    | ~ r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3)
    | ~ r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2)
    | ~ r2_hidden(sK6(sK1,sK2,sK3,sK4,sK0),sK1)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f65,f92])).

fof(f92,plain,
    ( sK0 = k4_tarski(k4_tarski(k4_tarski(sK6(sK1,sK2,sK3,sK4,sK0),sK7(sK1,sK2,sK3,sK4,sK0)),sK8(sK1,sK2,sK3,sK4,sK0)),sK9(sK1,sK2,sK3,sK4,sK0))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f75,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k4_tarski(k4_tarski(k4_tarski(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f64,f58,f59])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4
            & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
            & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
            & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
            & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f28,f39,f38,f37,f36])).

fof(f36,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( k4_mcart_1(X5,X6,X7,X8) = X4
                      & m1_subset_1(X8,X3) )
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                    & m1_subset_1(X8,X3) )
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( ? [X8] :
                ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4
                & m1_subset_1(X8,X3) )
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4
              & m1_subset_1(X8,X3) )
          & m1_subset_1(X7,X2) )
     => ( ? [X8] :
            ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4
            & m1_subset_1(X8,X3) )
        & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( k4_mcart_1(X5,X6,X7,X8) = X4
                          & m1_subset_1(X8,X3) )
                      & m1_subset_1(X7,X2) )
                  & m1_subset_1(X6,X1) )
              & m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ! [X6] :
                    ( m1_subset_1(X6,X1)
                   => ! [X7] :
                        ( m1_subset_1(X7,X2)
                       => ! [X8] :
                            ( m1_subset_1(X8,X3)
                           => k4_mcart_1(X5,X6,X7,X8) != X4 ) ) ) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).

fof(f75,plain,(
    m1_subset_1(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(unit_resulting_resolution,[],[f66,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f65,plain,(
    ! [X6,X8,X7,X5] :
      ( sK0 != k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)
      | ~ r2_hidden(X8,sK4)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(definition_unfolding,[],[f42,f58])).

fof(f42,plain,(
    ! [X6,X8,X7,X5] :
      ( k4_mcart_1(X5,X6,X7,X8) != sK0
      | ~ r2_hidden(X8,sK4)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f164,plain,(
    k1_xboole_0 != sK2 ),
    inference(superposition,[],[f138,f43])).

fof(f138,plain,(
    k1_xboole_0 != k3_xboole_0(sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f132,f56])).

fof(f132,plain,(
    ~ r1_xboole_0(sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f72,f125,f47])).

% (26420)Refutation not found, incomplete strategy% (26420)------------------------------
% (26420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f125,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f111,f49])).

% (26420)Termination reason: Refutation not found, incomplete strategy
fof(f111,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f80,f48])).

% (26420)Memory used [KB]: 1663
fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

% (26420)Time elapsed: 0.138 s
% (26420)------------------------------
% (26420)------------------------------
fof(f22,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f80,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(unit_resulting_resolution,[],[f74,f48])).

fof(f152,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4) ),
    inference(subsumption_resolution,[],[f151,f79])).

fof(f151,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK4)
    | r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4) ),
    inference(subsumption_resolution,[],[f150,f148])).

fof(f150,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK4)
    | r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4) ),
    inference(subsumption_resolution,[],[f149,f98])).

fof(f149,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK4)
    | r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4) ),
    inference(resolution,[],[f91,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f91,plain,
    ( m1_subset_1(sK9(sK1,sK2,sK3,sK4,sK0),sK4)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f75,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f63,f59])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f148,plain,(
    k1_xboole_0 != sK3 ),
    inference(superposition,[],[f120,f43])).

fof(f120,plain,(
    k1_xboole_0 != k3_xboole_0(sK3,sK3) ),
    inference(unit_resulting_resolution,[],[f119,f56])).

fof(f119,plain,(
    ~ r1_xboole_0(sK3,sK3) ),
    inference(unit_resulting_resolution,[],[f72,f110,f47])).

fof(f110,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(unit_resulting_resolution,[],[f80,f49])).

fof(f143,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3) ),
    inference(subsumption_resolution,[],[f142,f110])).

fof(f142,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK3)
    | r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3) ),
    inference(subsumption_resolution,[],[f141,f98])).

fof(f141,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK3)
    | r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3) ),
    inference(resolution,[],[f90,f51])).

fof(f90,plain,
    ( m1_subset_1(sK8(sK1,sK2,sK3,sK4,sK0),sK3)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f75,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f62,f59])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f135,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2) ),
    inference(subsumption_resolution,[],[f134,f125])).

fof(f134,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK2)
    | r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2) ),
    inference(subsumption_resolution,[],[f133,f98])).

fof(f133,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK2)
    | r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2) ),
    inference(resolution,[],[f89,f51])).

fof(f89,plain,
    ( m1_subset_1(sK7(sK1,sK2,sK3,sK4,sK0),sK2)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f75,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f61,f59])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f126,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(unit_resulting_resolution,[],[f111,f48])).

fof(f124,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK1)
    | r2_hidden(sK6(sK1,sK2,sK3,sK4,sK0),sK1) ),
    inference(subsumption_resolution,[],[f123,f98])).

fof(f123,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK1)
    | r2_hidden(sK6(sK1,sK2,sK3,sK4,sK0),sK1) ),
    inference(resolution,[],[f88,f51])).

fof(f88,plain,
    ( m1_subset_1(sK6(sK1,sK2,sK3,sK4,sK0),sK1)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f75,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f60,f59])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f144,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f137,f56])).

fof(f137,plain,(
    ~ r1_xboole_0(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f72,f126,f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (26405)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.48  % (26413)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.49  % (26405)Refutation not found, incomplete strategy% (26405)------------------------------
% 0.20/0.49  % (26405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (26405)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (26405)Memory used [KB]: 1791
% 0.20/0.49  % (26405)Time elapsed: 0.078 s
% 0.20/0.49  % (26405)------------------------------
% 0.20/0.49  % (26405)------------------------------
% 0.20/0.53  % (26397)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (26418)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.54  % (26392)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.38/0.54  % (26394)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.38/0.54  % (26392)Refutation not found, incomplete strategy% (26392)------------------------------
% 1.38/0.54  % (26392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (26392)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (26392)Memory used [KB]: 1663
% 1.38/0.54  % (26392)Time elapsed: 0.131 s
% 1.38/0.54  % (26392)------------------------------
% 1.38/0.54  % (26392)------------------------------
% 1.38/0.54  % (26391)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.38/0.54  % (26401)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.38/0.54  % (26402)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.54  % (26410)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.38/0.54  % (26415)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.54  % (26399)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.38/0.55  % (26402)Refutation found. Thanks to Tanya!
% 1.38/0.55  % SZS status Theorem for theBenchmark
% 1.38/0.55  % SZS output start Proof for theBenchmark
% 1.38/0.55  fof(f196,plain,(
% 1.38/0.55    $false),
% 1.38/0.55    inference(subsumption_resolution,[],[f192,f43])).
% 1.38/0.55  fof(f43,plain,(
% 1.38/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f16])).
% 1.38/0.55  fof(f16,plain,(
% 1.38/0.55    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.38/0.55    inference(rectify,[],[f2])).
% 1.38/0.55  fof(f2,axiom,(
% 1.38/0.55    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.38/0.55  fof(f192,plain,(
% 1.38/0.55    k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.38/0.55    inference(backward_demodulation,[],[f144,f175])).
% 1.38/0.55  % (26420)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.38/0.55  fof(f175,plain,(
% 1.38/0.55    k1_xboole_0 = sK1),
% 1.38/0.55    inference(global_subsumption,[],[f124,f126,f135,f143,f148,f152,f164,f174])).
% 1.38/0.55  fof(f174,plain,(
% 1.38/0.55    ~r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4) | ~r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3) | ~r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2) | ~r2_hidden(sK6(sK1,sK2,sK3,sK4,sK0),sK1) | k1_xboole_0 = sK1),
% 1.38/0.55    inference(subsumption_resolution,[],[f173,f164])).
% 1.38/0.55  fof(f173,plain,(
% 1.38/0.55    ~r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4) | ~r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3) | ~r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2) | ~r2_hidden(sK6(sK1,sK2,sK3,sK4,sK0),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.38/0.55    inference(subsumption_resolution,[],[f172,f148])).
% 1.38/0.55  fof(f172,plain,(
% 1.38/0.55    ~r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4) | ~r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3) | ~r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2) | ~r2_hidden(sK6(sK1,sK2,sK3,sK4,sK0),sK1) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.38/0.55    inference(subsumption_resolution,[],[f168,f98])).
% 1.38/0.55  fof(f98,plain,(
% 1.38/0.55    k1_xboole_0 != sK4),
% 1.38/0.55    inference(superposition,[],[f94,f43])).
% 1.38/0.55  fof(f94,plain,(
% 1.38/0.55    k1_xboole_0 != k3_xboole_0(sK4,sK4)),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f86,f56])).
% 1.38/0.55  fof(f56,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f35])).
% 1.38/0.55  fof(f35,plain,(
% 1.38/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.38/0.55    inference(nnf_transformation,[],[f1])).
% 1.38/0.55  fof(f1,axiom,(
% 1.38/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.38/0.55  fof(f86,plain,(
% 1.38/0.55    ~r1_xboole_0(sK4,sK4)),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f72,f79,f47])).
% 1.38/0.55  fof(f47,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f21])).
% 1.38/0.55  fof(f21,plain,(
% 1.38/0.55    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.38/0.55    inference(flattening,[],[f20])).
% 1.38/0.55  fof(f20,plain,(
% 1.38/0.55    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.38/0.55    inference(ennf_transformation,[],[f5])).
% 1.38/0.55  fof(f5,axiom,(
% 1.38/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.38/0.55  fof(f79,plain,(
% 1.38/0.55    ~v1_xboole_0(sK4)),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f74,f49])).
% 1.38/0.55  fof(f49,plain,(
% 1.38/0.55    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f23])).
% 1.38/0.55  fof(f23,plain,(
% 1.38/0.55    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 1.38/0.55    inference(ennf_transformation,[],[f7])).
% 1.38/0.55  fof(f7,axiom,(
% 1.38/0.55    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 1.38/0.55  fof(f74,plain,(
% 1.38/0.55    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f66,f57])).
% 1.38/0.55  fof(f57,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f27])).
% 1.38/0.55  fof(f27,plain,(
% 1.38/0.55    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 1.38/0.55    inference(ennf_transformation,[],[f6])).
% 1.38/0.55  fof(f6,axiom,(
% 1.38/0.55    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 1.38/0.55  fof(f66,plain,(
% 1.38/0.55    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 1.38/0.55    inference(definition_unfolding,[],[f41,f59])).
% 1.38/0.55  fof(f59,plain,(
% 1.38/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f13])).
% 1.38/0.55  fof(f13,axiom,(
% 1.38/0.55    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).
% 1.38/0.55  fof(f41,plain,(
% 1.38/0.55    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 1.38/0.55    inference(cnf_transformation,[],[f30])).
% 1.38/0.55  fof(f30,plain,(
% 1.38/0.55    ! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != sK0 | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 1.38/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f29])).
% 1.38/0.55  fof(f29,plain,(
% 1.38/0.55    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4))) => (! [X8,X7,X6,X5] : (k4_mcart_1(X5,X6,X7,X8) != sK0 | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f18,plain,(
% 1.38/0.55    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 1.38/0.55    inference(ennf_transformation,[],[f15])).
% 1.38/0.55  fof(f15,negated_conjecture,(
% 1.38/0.55    ~! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 1.38/0.55    inference(negated_conjecture,[],[f14])).
% 1.38/0.55  fof(f14,conjecture,(
% 1.38/0.55    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).
% 1.38/0.55  fof(f72,plain,(
% 1.38/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.38/0.55    inference(equality_resolution,[],[f53])).
% 1.38/0.55  fof(f53,plain,(
% 1.38/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.38/0.55    inference(cnf_transformation,[],[f34])).
% 1.38/0.55  fof(f34,plain,(
% 1.38/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.55    inference(flattening,[],[f33])).
% 1.38/0.55  fof(f33,plain,(
% 1.38/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.55    inference(nnf_transformation,[],[f4])).
% 1.38/0.55  fof(f4,axiom,(
% 1.38/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.38/0.55  fof(f168,plain,(
% 1.38/0.55    ~r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4) | ~r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3) | ~r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2) | ~r2_hidden(sK6(sK1,sK2,sK3,sK4,sK0),sK1) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.38/0.55    inference(trivial_inequality_removal,[],[f166])).
% 1.38/0.55  fof(f166,plain,(
% 1.38/0.55    sK0 != sK0 | ~r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4) | ~r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3) | ~r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2) | ~r2_hidden(sK6(sK1,sK2,sK3,sK4,sK0),sK1) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.38/0.55    inference(superposition,[],[f65,f92])).
% 1.38/0.55  fof(f92,plain,(
% 1.38/0.55    sK0 = k4_tarski(k4_tarski(k4_tarski(sK6(sK1,sK2,sK3,sK4,sK0),sK7(sK1,sK2,sK3,sK4,sK0)),sK8(sK1,sK2,sK3,sK4,sK0)),sK9(sK1,sK2,sK3,sK4,sK0)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.38/0.55    inference(resolution,[],[f75,f67])).
% 1.38/0.55  fof(f67,plain,(
% 1.38/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k4_tarski(k4_tarski(k4_tarski(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.38/0.55    inference(definition_unfolding,[],[f64,f58,f59])).
% 1.38/0.55  fof(f58,plain,(
% 1.38/0.55    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f12])).
% 1.38/0.55  fof(f12,axiom,(
% 1.38/0.55    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).
% 1.38/0.55  fof(f64,plain,(
% 1.38/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f40])).
% 1.38/0.55  fof(f40,plain,(
% 1.38/0.55    ! [X0,X1,X2,X3] : (! [X4] : (((((k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)) & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.38/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f28,f39,f38,f37,f36])).
% 1.38/0.55  fof(f36,plain,(
% 1.38/0.55    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f37,plain,(
% 1.38/0.55    ! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) => (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f38,plain,(
% 1.38/0.55    ! [X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) => (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f39,plain,(
% 1.38/0.55    ! [X4,X3,X2,X1,X0] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) => (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f28,plain,(
% 1.38/0.55    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.38/0.55    inference(ennf_transformation,[],[f11])).
% 1.38/0.55  fof(f11,axiom,(
% 1.38/0.55    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).
% 1.38/0.55  fof(f75,plain,(
% 1.38/0.55    m1_subset_1(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f66,f50])).
% 1.38/0.55  fof(f50,plain,(
% 1.38/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f24])).
% 1.38/0.55  fof(f24,plain,(
% 1.38/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.38/0.55    inference(ennf_transformation,[],[f9])).
% 1.38/0.55  fof(f9,axiom,(
% 1.38/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.38/0.55  fof(f65,plain,(
% 1.38/0.55    ( ! [X6,X8,X7,X5] : (sK0 != k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) )),
% 1.38/0.55    inference(definition_unfolding,[],[f42,f58])).
% 1.38/0.55  fof(f42,plain,(
% 1.38/0.55    ( ! [X6,X8,X7,X5] : (k4_mcart_1(X5,X6,X7,X8) != sK0 | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f30])).
% 1.38/0.55  fof(f164,plain,(
% 1.38/0.55    k1_xboole_0 != sK2),
% 1.38/0.55    inference(superposition,[],[f138,f43])).
% 1.38/0.55  fof(f138,plain,(
% 1.38/0.55    k1_xboole_0 != k3_xboole_0(sK2,sK2)),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f132,f56])).
% 1.38/0.55  fof(f132,plain,(
% 1.38/0.55    ~r1_xboole_0(sK2,sK2)),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f72,f125,f47])).
% 1.38/0.55  % (26420)Refutation not found, incomplete strategy% (26420)------------------------------
% 1.38/0.55  % (26420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  fof(f125,plain,(
% 1.38/0.55    ~v1_xboole_0(sK2)),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f111,f49])).
% 1.38/0.55  % (26420)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  fof(f111,plain,(
% 1.38/0.55    ~v1_xboole_0(k2_zfmisc_1(sK1,sK2))),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f80,f48])).
% 1.38/0.55  
% 1.38/0.55  % (26420)Memory used [KB]: 1663
% 1.38/0.55  fof(f48,plain,(
% 1.38/0.55    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f22])).
% 1.38/0.55  % (26420)Time elapsed: 0.138 s
% 1.38/0.55  % (26420)------------------------------
% 1.38/0.55  % (26420)------------------------------
% 1.38/0.55  fof(f22,plain,(
% 1.38/0.55    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.38/0.55    inference(ennf_transformation,[],[f8])).
% 1.38/0.55  fof(f8,axiom,(
% 1.38/0.55    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.38/0.55  fof(f80,plain,(
% 1.38/0.55    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f74,f48])).
% 1.38/0.55  fof(f152,plain,(
% 1.38/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4)),
% 1.38/0.55    inference(subsumption_resolution,[],[f151,f79])).
% 1.38/0.55  fof(f151,plain,(
% 1.38/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_xboole_0(sK4) | r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4)),
% 1.38/0.55    inference(subsumption_resolution,[],[f150,f148])).
% 1.38/0.55  fof(f150,plain,(
% 1.38/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_xboole_0(sK4) | r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4)),
% 1.38/0.55    inference(subsumption_resolution,[],[f149,f98])).
% 1.38/0.55  fof(f149,plain,(
% 1.38/0.55    k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_xboole_0(sK4) | r2_hidden(sK9(sK1,sK2,sK3,sK4,sK0),sK4)),
% 1.38/0.55    inference(resolution,[],[f91,f51])).
% 1.38/0.55  fof(f51,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f26])).
% 1.38/0.55  fof(f26,plain,(
% 1.38/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.38/0.55    inference(flattening,[],[f25])).
% 1.38/0.55  fof(f25,plain,(
% 1.38/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.38/0.55    inference(ennf_transformation,[],[f10])).
% 1.38/0.55  fof(f10,axiom,(
% 1.38/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.38/0.55  fof(f91,plain,(
% 1.38/0.55    m1_subset_1(sK9(sK1,sK2,sK3,sK4,sK0),sK4) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.38/0.55    inference(resolution,[],[f75,f68])).
% 1.38/0.55  fof(f68,plain,(
% 1.38/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.38/0.55    inference(definition_unfolding,[],[f63,f59])).
% 1.38/0.55  fof(f63,plain,(
% 1.38/0.55    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f40])).
% 1.38/0.55  fof(f148,plain,(
% 1.38/0.55    k1_xboole_0 != sK3),
% 1.38/0.55    inference(superposition,[],[f120,f43])).
% 1.38/0.55  fof(f120,plain,(
% 1.38/0.55    k1_xboole_0 != k3_xboole_0(sK3,sK3)),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f119,f56])).
% 1.38/0.55  fof(f119,plain,(
% 1.38/0.55    ~r1_xboole_0(sK3,sK3)),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f72,f110,f47])).
% 1.38/0.55  fof(f110,plain,(
% 1.38/0.55    ~v1_xboole_0(sK3)),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f80,f49])).
% 1.38/0.55  fof(f143,plain,(
% 1.38/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3)),
% 1.38/0.55    inference(subsumption_resolution,[],[f142,f110])).
% 1.38/0.55  fof(f142,plain,(
% 1.38/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_xboole_0(sK3) | r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3)),
% 1.38/0.55    inference(subsumption_resolution,[],[f141,f98])).
% 1.38/0.55  fof(f141,plain,(
% 1.38/0.55    k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_xboole_0(sK3) | r2_hidden(sK8(sK1,sK2,sK3,sK4,sK0),sK3)),
% 1.38/0.55    inference(resolution,[],[f90,f51])).
% 1.38/0.55  fof(f90,plain,(
% 1.38/0.55    m1_subset_1(sK8(sK1,sK2,sK3,sK4,sK0),sK3) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.38/0.55    inference(resolution,[],[f75,f69])).
% 1.38/0.55  fof(f69,plain,(
% 1.38/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.38/0.55    inference(definition_unfolding,[],[f62,f59])).
% 1.38/0.55  fof(f62,plain,(
% 1.38/0.55    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f40])).
% 1.38/0.55  fof(f135,plain,(
% 1.38/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2)),
% 1.38/0.55    inference(subsumption_resolution,[],[f134,f125])).
% 1.38/0.55  fof(f134,plain,(
% 1.38/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_xboole_0(sK2) | r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2)),
% 1.38/0.55    inference(subsumption_resolution,[],[f133,f98])).
% 1.38/0.55  fof(f133,plain,(
% 1.38/0.55    k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_xboole_0(sK2) | r2_hidden(sK7(sK1,sK2,sK3,sK4,sK0),sK2)),
% 1.38/0.55    inference(resolution,[],[f89,f51])).
% 1.38/0.55  fof(f89,plain,(
% 1.38/0.55    m1_subset_1(sK7(sK1,sK2,sK3,sK4,sK0),sK2) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.38/0.55    inference(resolution,[],[f75,f70])).
% 1.38/0.55  fof(f70,plain,(
% 1.38/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.38/0.55    inference(definition_unfolding,[],[f61,f59])).
% 1.38/0.55  fof(f61,plain,(
% 1.38/0.55    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f40])).
% 1.38/0.55  fof(f126,plain,(
% 1.38/0.55    ~v1_xboole_0(sK1)),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f111,f48])).
% 1.38/0.55  fof(f124,plain,(
% 1.38/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_xboole_0(sK1) | r2_hidden(sK6(sK1,sK2,sK3,sK4,sK0),sK1)),
% 1.38/0.55    inference(subsumption_resolution,[],[f123,f98])).
% 1.38/0.55  fof(f123,plain,(
% 1.38/0.55    k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_xboole_0(sK1) | r2_hidden(sK6(sK1,sK2,sK3,sK4,sK0),sK1)),
% 1.38/0.55    inference(resolution,[],[f88,f51])).
% 1.38/0.55  fof(f88,plain,(
% 1.38/0.55    m1_subset_1(sK6(sK1,sK2,sK3,sK4,sK0),sK1) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.38/0.55    inference(resolution,[],[f75,f71])).
% 1.38/0.55  fof(f71,plain,(
% 1.38/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.38/0.55    inference(definition_unfolding,[],[f60,f59])).
% 1.38/0.55  fof(f60,plain,(
% 1.38/0.55    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f40])).
% 1.38/0.55  fof(f144,plain,(
% 1.38/0.55    k1_xboole_0 != k3_xboole_0(sK1,sK1)),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f137,f56])).
% 1.38/0.55  fof(f137,plain,(
% 1.38/0.55    ~r1_xboole_0(sK1,sK1)),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f72,f126,f47])).
% 1.38/0.55  % SZS output end Proof for theBenchmark
% 1.38/0.55  % (26402)------------------------------
% 1.38/0.55  % (26402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (26402)Termination reason: Refutation
% 1.38/0.55  
% 1.38/0.55  % (26402)Memory used [KB]: 6524
% 1.38/0.55  % (26402)Time elapsed: 0.138 s
% 1.38/0.55  % (26402)------------------------------
% 1.38/0.55  % (26402)------------------------------
% 1.38/0.55  % (26404)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.38/0.55  % (26400)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.38/0.55  % (26398)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.55  % (26416)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.55  % (26407)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.55  % (26407)Refutation not found, incomplete strategy% (26407)------------------------------
% 1.38/0.55  % (26407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (26395)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.38/0.56  % (26393)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.50/0.56  % (26408)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.50/0.56  % (26407)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (26407)Memory used [KB]: 10618
% 1.50/0.56  % (26407)Time elapsed: 0.147 s
% 1.50/0.56  % (26407)------------------------------
% 1.50/0.56  % (26407)------------------------------
% 1.50/0.56  % (26401)Refutation not found, incomplete strategy% (26401)------------------------------
% 1.50/0.56  % (26401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (26401)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (26401)Memory used [KB]: 10746
% 1.50/0.56  % (26401)Time elapsed: 0.150 s
% 1.50/0.56  % (26401)------------------------------
% 1.50/0.56  % (26401)------------------------------
% 1.50/0.56  % (26406)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.50/0.56  % (26396)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.50/0.56  % (26417)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.50/0.57  % (26412)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.50/0.57  % (26390)Success in time 0.207 s
%------------------------------------------------------------------------------
