%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0374+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:51 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 109 expanded)
%              Number of leaves         :    7 (  24 expanded)
%              Depth                    :   19
%              Number of atoms          :  117 ( 327 expanded)
%              Number of equality atoms :   32 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(subsumption_resolution,[],[f139,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( k1_xboole_0 != X0
             => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ( k1_xboole_0 != X0
           => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

fof(f139,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f135,f19])).

fof(f19,plain,(
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

fof(f135,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f134,f48])).

fof(f48,plain,(
    ~ r2_hidden(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f47,f31])).

fof(f31,plain,(
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

fof(f47,plain,
    ( ~ r2_hidden(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f22,f17])).

fof(f17,plain,(
    ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f134,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f132,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f132,plain,
    ( r1_tarski(k2_tarski(sK1,sK2),sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f130,f50])).

fof(f50,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f23,f18])).

fof(f18,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f130,plain,
    ( ~ r2_hidden(sK1,sK0)
    | r1_tarski(k2_tarski(sK1,sK2),sK0) ),
    inference(superposition,[],[f26,f128])).

fof(f128,plain,(
    sK1 = sK3(k2_tarski(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f127,f16])).

fof(f127,plain,
    ( sK1 = sK3(k2_tarski(sK1,sK2),sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f123,f19])).

fof(f123,plain,
    ( v1_xboole_0(sK0)
    | sK1 = sK3(k2_tarski(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f122,f48])).

fof(f122,plain,
    ( sK1 = sK3(k2_tarski(sK1,sK2),sK0)
    | v1_xboole_0(sK0)
    | r2_hidden(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f120,f39])).

fof(f120,plain,
    ( r1_tarski(k2_tarski(sK1,sK2),sK0)
    | sK1 = sK3(k2_tarski(sK1,sK2),sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f116,f49])).

fof(f49,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f23,f15])).

fof(f15,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f116,plain,
    ( ~ r2_hidden(sK2,sK0)
    | r1_tarski(k2_tarski(sK1,sK2),sK0)
    | sK1 = sK3(k2_tarski(sK1,sK2),sK0) ),
    inference(superposition,[],[f26,f114])).

fof(f114,plain,
    ( sK2 = sK3(k2_tarski(sK1,sK2),sK0)
    | sK1 = sK3(k2_tarski(sK1,sK2),sK0) ),
    inference(resolution,[],[f99,f48])).

fof(f99,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(k2_tarski(X4,X5),k1_zfmisc_1(X6))
      | sK3(k2_tarski(X4,X5),X6) = X5
      | sK3(k2_tarski(X4,X5),X6) = X4 ) ),
    inference(resolution,[],[f63,f39])).

fof(f63,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k2_tarski(X5,X4),X6)
      | sK3(k2_tarski(X5,X4),X6) = X5
      | sK3(k2_tarski(X5,X4),X6) = X4 ) ),
    inference(resolution,[],[f44,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
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

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
