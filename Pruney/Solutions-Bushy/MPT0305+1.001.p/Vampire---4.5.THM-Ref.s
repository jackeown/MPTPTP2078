%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0305+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  70 expanded)
%              Number of leaves         :    4 (  17 expanded)
%              Depth                    :   21
%              Number of atoms          :  107 ( 212 expanded)
%              Number of equality atoms :    9 (  25 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(subsumption_resolution,[],[f110,f11])).

fof(f11,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X1,X2)
      & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_tarski(X1,X2)
          & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
            | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f110,plain,(
    r1_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( r1_tarski(sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f108,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f108,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f107,f11])).

fof(f107,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | r1_tarski(sK1,sK2) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | r1_tarski(sK1,sK2)
      | r1_tarski(sK1,sK2) ) ),
    inference(resolution,[],[f85,f15])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(sK1,X1),sK2)
      | r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f83,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f83,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(sK1,X2),sK2)
      | r2_hidden(k4_tarski(sK3(sK0),sK4(sK1,X3)),k2_zfmisc_1(sK0,sK2))
      | r1_tarski(sK1,X2)
      | r1_tarski(sK1,X3) ) ),
    inference(subsumption_resolution,[],[f81,f10])).

fof(f10,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(sK1,X2),sK2)
      | r1_tarski(sK1,X2)
      | r2_hidden(k4_tarski(sK3(sK0),sK4(sK1,X3)),k2_zfmisc_1(sK0,sK2))
      | r1_tarski(sK1,X3)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f59,f12])).

fof(f12,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f59,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | r2_hidden(sK4(sK1,X4),sK2)
      | r1_tarski(sK1,X4)
      | r2_hidden(k4_tarski(X2,sK4(sK1,X3)),k2_zfmisc_1(sK0,sK2))
      | r1_tarski(sK1,X3) ) ),
    inference(resolution,[],[f51,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(sK0,sK2))
      | r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f49,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_zfmisc_1(sK0,sK1))
      | r1_tarski(sK1,X0)
      | r2_hidden(X1,k2_zfmisc_1(sK0,sK2))
      | r2_hidden(sK4(sK1,X0),sK2) ) ),
    inference(resolution,[],[f48,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0] :
      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
      | r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f46,f10])).

fof(f46,plain,(
    ! [X0] :
      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
      | r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f31,f12])).

fof(f31,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,sK0)
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
      | r2_hidden(sK4(sK1,X2),sK2)
      | r1_tarski(sK1,X2) ) ),
    inference(resolution,[],[f29,f14])).

fof(f29,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X2,sK0)
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
      | r2_hidden(X3,sK2) ) ),
    inference(resolution,[],[f25,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK0))
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f22,f18])).

fof(f22,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(sK1,sK0))
      | r2_hidden(X0,k2_zfmisc_1(sK2,sK0))
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) ) ),
    inference(resolution,[],[f9,f13])).

fof(f9,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
