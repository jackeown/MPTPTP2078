%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0375+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:51 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 152 expanded)
%              Number of leaves         :    7 (  33 expanded)
%              Depth                    :   25
%              Number of atoms          :  155 ( 512 expanded)
%              Number of equality atoms :   55 ( 105 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f527,plain,(
    $false ),
    inference(subsumption_resolution,[],[f526,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( k1_xboole_0 != X0
                 => m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ( k1_xboole_0 != X0
               => m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_subset_1)).

fof(f526,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f522,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f522,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f521,f55])).

fof(f55,plain,(
    ~ r2_hidden(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f54,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f54,plain,
    ( ~ r2_hidden(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f24,f18])).

fof(f18,plain,(
    ~ m1_subset_1(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f521,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f517,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f517,plain,
    ( r1_tarski(k1_enumset1(sK1,sK2,sK3),sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f515,f58])).

fof(f58,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f25,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f515,plain,
    ( ~ r2_hidden(sK1,sK0)
    | r1_tarski(k1_enumset1(sK1,sK2,sK3),sK0) ),
    inference(superposition,[],[f28,f514])).

fof(f514,plain,(
    sK1 = sK4(k1_enumset1(sK1,sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f513,f17])).

fof(f513,plain,
    ( sK1 = sK4(k1_enumset1(sK1,sK2,sK3),sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f509,f21])).

fof(f509,plain,
    ( v1_xboole_0(sK0)
    | sK1 = sK4(k1_enumset1(sK1,sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f508,f55])).

fof(f508,plain,
    ( sK1 = sK4(k1_enumset1(sK1,sK2,sK3),sK0)
    | v1_xboole_0(sK0)
    | r2_hidden(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f506,f43])).

fof(f506,plain,
    ( r1_tarski(k1_enumset1(sK1,sK2,sK3),sK0)
    | sK1 = sK4(k1_enumset1(sK1,sK2,sK3),sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f502,f57])).

fof(f57,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f25,f19])).

fof(f19,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f502,plain,
    ( ~ r2_hidden(sK2,sK0)
    | r1_tarski(k1_enumset1(sK1,sK2,sK3),sK0)
    | sK1 = sK4(k1_enumset1(sK1,sK2,sK3),sK0) ),
    inference(superposition,[],[f28,f499])).

fof(f499,plain,
    ( sK2 = sK4(k1_enumset1(sK1,sK2,sK3),sK0)
    | sK1 = sK4(k1_enumset1(sK1,sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f498,f17])).

fof(f498,plain,
    ( sK1 = sK4(k1_enumset1(sK1,sK2,sK3),sK0)
    | sK2 = sK4(k1_enumset1(sK1,sK2,sK3),sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f494,f21])).

fof(f494,plain,
    ( v1_xboole_0(sK0)
    | sK1 = sK4(k1_enumset1(sK1,sK2,sK3),sK0)
    | sK2 = sK4(k1_enumset1(sK1,sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f493,f55])).

fof(f493,plain,
    ( sK2 = sK4(k1_enumset1(sK1,sK2,sK3),sK0)
    | sK1 = sK4(k1_enumset1(sK1,sK2,sK3),sK0)
    | v1_xboole_0(sK0)
    | r2_hidden(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f491,f43])).

fof(f491,plain,
    ( r1_tarski(k1_enumset1(sK1,sK2,sK3),sK0)
    | sK2 = sK4(k1_enumset1(sK1,sK2,sK3),sK0)
    | sK1 = sK4(k1_enumset1(sK1,sK2,sK3),sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f485,f56])).

fof(f56,plain,
    ( r2_hidden(sK3,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f25,f16])).

fof(f16,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f485,plain,
    ( ~ r2_hidden(sK3,sK0)
    | r1_tarski(k1_enumset1(sK1,sK2,sK3),sK0)
    | sK2 = sK4(k1_enumset1(sK1,sK2,sK3),sK0)
    | sK1 = sK4(k1_enumset1(sK1,sK2,sK3),sK0) ),
    inference(superposition,[],[f28,f483])).

fof(f483,plain,
    ( sK3 = sK4(k1_enumset1(sK1,sK2,sK3),sK0)
    | sK2 = sK4(k1_enumset1(sK1,sK2,sK3),sK0)
    | sK1 = sK4(k1_enumset1(sK1,sK2,sK3),sK0) ),
    inference(resolution,[],[f236,f55])).

fof(f236,plain,(
    ! [X6,X8,X7,X5] :
      ( r2_hidden(k1_enumset1(X5,X6,X7),k1_zfmisc_1(X8))
      | sK4(k1_enumset1(X5,X6,X7),X8) = X5
      | sK4(k1_enumset1(X5,X6,X7),X8) = X6
      | sK4(k1_enumset1(X5,X6,X7),X8) = X7 ) ),
    inference(resolution,[],[f79,f43])).

fof(f79,plain,(
    ! [X12,X10,X11,X9] :
      ( r1_tarski(k1_enumset1(X10,X9,X11),X12)
      | sK4(k1_enumset1(X10,X9,X11),X12) = X11
      | sK4(k1_enumset1(X10,X9,X11),X12) = X10
      | sK4(k1_enumset1(X10,X9,X11),X12) = X9 ) ),
    inference(resolution,[],[f50,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
