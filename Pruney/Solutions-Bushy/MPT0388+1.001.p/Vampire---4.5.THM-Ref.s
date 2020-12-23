%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0388+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  47 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :   13
%              Number of atoms          :   87 ( 164 expanded)
%              Number of equality atoms :   24 (  47 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(subsumption_resolution,[],[f51,f11])).

fof(f11,plain,(
    ~ r1_tarski(sK1,k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X1,k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X1,k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r1_tarski(X1,X2) )
       => ( r1_tarski(X1,k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f51,plain,(
    r1_tarski(sK1,k1_setfam_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,
    ( r1_tarski(sK1,k1_setfam_1(sK0))
    | r1_tarski(sK1,k1_setfam_1(sK0)) ),
    inference(resolution,[],[f48,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f48,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK1,X1),k1_setfam_1(sK0))
      | r1_tarski(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f46,f10])).

fof(f10,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK1,X1),k1_setfam_1(sK0))
      | r1_tarski(sK1,X1)
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f44])).

fof(f44,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK1,X1),k1_setfam_1(sK0))
      | r1_tarski(sK1,X1)
      | k1_xboole_0 = sK0
      | r2_hidden(sK5(sK1,X1),k1_setfam_1(sK0)) ) ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,sK3(X0,X2))
      | k1_xboole_0 = X0
      | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X2,sK3(X0,X2))
      | r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(sK1,X1),sK3(sK0,X0))
      | r2_hidden(X0,k1_setfam_1(sK0))
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f41,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK5(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0] :
      ( r1_tarski(sK1,sK3(sK0,X0))
      | r2_hidden(X0,k1_setfam_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f39,f10])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | r2_hidden(X0,k1_setfam_1(sK0))
      | r1_tarski(sK1,sK3(sK0,X0)) ) ),
    inference(resolution,[],[f28,f9])).

fof(f9,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | r1_tarski(sK1,X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),X0)
      | k1_xboole_0 = X0
      | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X2),X0)
      | r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
