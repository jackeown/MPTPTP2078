%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1611+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:26 EST 2020

% Result     : Theorem 3.98s
% Output     : Refutation 4.79s
% Verified   : 
% Statistics : Number of formulae       :   45 (  45 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 112 expanded)
%              Number of equality atoms :   47 (  47 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6883,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6877,f4267])).

fof(f4267,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f3118])).

fof(f3118,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f22])).

% (7248)Refutation not found, incomplete strategy% (7248)------------------------------
% (7248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7248)Termination reason: Refutation not found, incomplete strategy

% (7248)Memory used [KB]: 10490
% (7248)Time elapsed: 0.261 s
% (7248)------------------------------
% (7248)------------------------------
fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f6877,plain,(
    k1_tarski(sK14) != k2_xboole_0(k1_tarski(sK14),k1_tarski(sK14)) ),
    inference(backward_demodulation,[],[f6792,f6876])).

fof(f6876,plain,(
    ! [X5] : k4_yellow_0(k3_yellow_1(X5)) = X5 ),
    inference(forward_demodulation,[],[f6875,f4514])).

fof(f4514,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f3811,f4309])).

fof(f4309,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f1559])).

fof(f1559,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f3811,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f3105])).

fof(f3105,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f6875,plain,(
    ! [X5] : k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X5))) = X5 ),
    inference(subsumption_resolution,[],[f6874,f4070])).

fof(f4070,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f477])).

fof(f477,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f6874,plain,(
    ! [X5] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X5))) = X5
      | v1_xboole_0(k1_zfmisc_1(X5)) ) ),
    inference(subsumption_resolution,[],[f6870,f4788])).

fof(f4788,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f4420,f4418])).

fof(f4418,plain,(
    ! [X0,X3] :
      ( ~ r1_tarski(X3,X0)
      | r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f4081])).

fof(f4081,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3644])).

fof(f3644,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK92(X0,X1),X0)
            | ~ r2_hidden(sK92(X0,X1),X1) )
          & ( r1_tarski(sK92(X0,X1),X0)
            | r2_hidden(sK92(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK92])],[f3642,f3643])).

fof(f3643,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK92(X0,X1),X0)
          | ~ r2_hidden(sK92(X0,X1),X1) )
        & ( r1_tarski(sK92(X0,X1),X0)
          | r2_hidden(sK92(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f3642,plain,(
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
    inference(rectify,[],[f3641])).

% (7220)Refutation not found, incomplete strategy% (7220)------------------------------
% (7220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7220)Termination reason: Refutation not found, incomplete strategy

% (7220)Memory used [KB]: 12792
% (7220)Time elapsed: 0.537 s
% (7220)------------------------------
% (7220)------------------------------
fof(f3641,plain,(
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
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f4420,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f4088])).

fof(f4088,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3650])).

fof(f3650,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f3649])).

fof(f3649,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f6870,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_zfmisc_1(X5))
      | k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X5))) = X5
      | v1_xboole_0(k1_zfmisc_1(X5)) ) ),
    inference(superposition,[],[f3792,f4037])).

fof(f4037,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f448])).

fof(f448,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f3792,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3127])).

fof(f3127,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3126])).

fof(f3126,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3095])).

fof(f3095,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f6792,plain,(
    k1_tarski(sK14) != k2_xboole_0(k1_tarski(sK14),k1_tarski(k4_yellow_0(k3_yellow_1(sK14)))) ),
    inference(unit_resulting_resolution,[],[f3788,f4252])).

fof(f4252,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3350])).

fof(f3350,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f356])).

fof(f356,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f3788,plain,(
    sK14 != k4_yellow_0(k3_yellow_1(sK14)) ),
    inference(cnf_transformation,[],[f3454])).

fof(f3454,plain,(
    sK14 != k4_yellow_0(k3_yellow_1(sK14)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f3121,f3453])).

fof(f3453,plain,
    ( ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0
   => sK14 != k4_yellow_0(k3_yellow_1(sK14)) ),
    introduced(choice_axiom,[])).

fof(f3121,plain,(
    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f3101])).

fof(f3101,negated_conjecture,(
    ~ ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f3100])).

fof(f3100,conjecture,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).
%------------------------------------------------------------------------------
