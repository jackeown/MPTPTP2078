%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 223 expanded)
%              Number of leaves         :   10 (  72 expanded)
%              Depth                    :   23
%              Number of atoms          :  260 (1133 expanded)
%              Number of equality atoms :   25 (  41 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f284,plain,(
    $false ),
    inference(resolution,[],[f283,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
    & r1_xboole_0(sK3,sK2)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
                & r1_xboole_0(X3,X2)
                & r1_tarski(X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(sK1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
            & r1_xboole_0(X3,X2)
            & r1_tarski(sK1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ? [X3] :
          ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
          & r1_xboole_0(X3,sK2)
          & r1_tarski(sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
        & r1_xboole_0(X3,sK2)
        & r1_tarski(sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
      & r1_xboole_0(sK3,sK2)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

% (25271)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ( r1_xboole_0(X3,X2)
                    & r1_tarski(X1,X2) )
                 => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ( r1_xboole_0(X3,X2)
                  & r1_tarski(X1,X2) )
               => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).

fof(f283,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f276,f26])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f276,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f274,f46])).

fof(f46,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f31,f29])).

fof(f29,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f274,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f265,f210])).

fof(f210,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2))) ),
    inference(resolution,[],[f209,f25])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f209,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2))) ),
    inference(resolution,[],[f208,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f208,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2))) ),
    inference(resolution,[],[f207,f30])).

fof(f207,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2))) ),
    inference(resolution,[],[f203,f24])).

fof(f203,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2))) ),
    inference(resolution,[],[f202,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f202,plain,(
    r1_xboole_0(sK1,k3_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))) ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( sK1 != sK1
    | r1_xboole_0(sK1,k3_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))) ),
    inference(superposition,[],[f38,f198])).

fof(f198,plain,(
    sK1 = k4_xboole_0(sK1,k3_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))) ),
    inference(resolution,[],[f196,f24])).

fof(f196,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | sK1 = k4_xboole_0(sK1,k3_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))) ),
    inference(resolution,[],[f158,f66])).

fof(f66,plain,(
    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( sK1 != sK1
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f38,f62])).

fof(f62,plain,(
    sK1 = k4_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f61,f24])).

fof(f61,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | sK1 = k4_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f58,f25])).

fof(f58,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | sK1 = k4_xboole_0(sK1,k3_subset_1(X0,sK2)) ) ),
    inference(resolution,[],[f50,f27])).

fof(f27,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X5))
      | k4_xboole_0(X3,k3_subset_1(X5,X4)) = X3 ) ),
    inference(resolution,[],[f36,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f158,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,k3_subset_1(sK0,sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | k4_xboole_0(X1,k3_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))) = X1 ) ),
    inference(resolution,[],[f108,f25])).

fof(f108,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | ~ r1_xboole_0(X3,k3_subset_1(X4,X5))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | k4_xboole_0(X3,k3_subset_1(X4,k3_subset_1(X4,k3_subset_1(X4,X5)))) = X3 ) ),
    inference(resolution,[],[f102,f30])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k4_xboole_0(X0,k3_subset_1(X1,k3_subset_1(X1,X2))) = X0
      | ~ r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k4_xboole_0(X0,k3_subset_1(X1,k3_subset_1(X1,X2))) = X0
      | ~ r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f59,f30])).

fof(f59,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | k4_xboole_0(X4,k3_subset_1(X3,k3_subset_1(X1,X2))) = X4
      | ~ r1_xboole_0(X4,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f50,f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f265,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))
      | r1_xboole_0(X0,sK3) ) ),
    inference(superposition,[],[f40,f264])).

fof(f264,plain,(
    k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),sK3) ),
    inference(resolution,[],[f263,f26])).

fof(f263,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),sK3) ),
    inference(resolution,[],[f237,f28])).

fof(f28,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f237,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK2)
      | k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f193,f25])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k3_subset_1(X1,k3_subset_1(X1,X2)) = k4_xboole_0(k3_subset_1(X1,k3_subset_1(X1,X2)),X0)
      | ~ r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k3_subset_1(X1,k3_subset_1(X1,X2)) = k4_xboole_0(k3_subset_1(X1,k3_subset_1(X1,X2)),X0)
      | ~ r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f74,f30])).

fof(f74,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | k3_subset_1(X3,k3_subset_1(X1,X2)) = k4_xboole_0(k3_subset_1(X3,k3_subset_1(X1,X2)),X4)
      | ~ r1_xboole_0(X4,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f71,f31])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k3_subset_1(X1,X2) = k4_xboole_0(k3_subset_1(X1,X2),X0) ) ),
    inference(resolution,[],[f70,f37])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k3_subset_1(X1,X0),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | r1_xboole_0(k3_subset_1(X1,X0),X2)
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f53,f30])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | r1_xboole_0(k3_subset_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | r1_xboole_0(k3_subset_1(X2,X1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f33,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:01:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (25266)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.49  % (25274)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.50  % (25261)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (25267)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  % (25257)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (25260)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.51  % (25258)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.51  % (25256)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (25278)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.51  % (25277)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.51  % (25265)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.51  % (25270)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.52  % (25264)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.52  % (25268)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.52  % (25262)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.52  % (25259)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.52  % (25272)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.52  % (25269)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.52  % (25259)Refutation not found, incomplete strategy% (25259)------------------------------
% 0.20/0.52  % (25259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25259)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25259)Memory used [KB]: 10490
% 0.20/0.52  % (25259)Time elapsed: 0.102 s
% 0.20/0.52  % (25259)------------------------------
% 0.20/0.52  % (25259)------------------------------
% 0.20/0.53  % (25273)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.53  % (25276)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.53  % (25275)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.54  % (25263)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (25265)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f284,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(resolution,[],[f283,f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ((~r1_tarski(sK1,k3_subset_1(sK0,sK3)) & r1_xboole_0(sK3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f18,f17,f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ? [X2] : (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (~r1_tarski(sK1,k3_subset_1(sK0,sK3)) & r1_xboole_0(sK3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f10,plain,(
% 0.20/0.54    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(flattening,[],[f9])).
% 0.20/0.54  % (25271)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.54  fof(f9,plain,(
% 0.20/0.54    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(X1,k3_subset_1(X0,X3)) & (r1_xboole_0(X3,X2) & r1_tarski(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.20/0.54    inference(negated_conjecture,[],[f7])).
% 0.20/0.54  fof(f7,conjecture,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).
% 0.20/0.54  fof(f283,plain,(
% 0.20/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(resolution,[],[f276,f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f276,plain,(
% 0.20/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(resolution,[],[f274,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ~r1_xboole_0(sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(resolution,[],[f31,f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ~r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(nnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
% 0.20/0.54  fof(f274,plain,(
% 0.20/0.54    r1_xboole_0(sK1,sK3)),
% 0.20/0.54    inference(resolution,[],[f265,f210])).
% 0.20/0.54  fof(f210,plain,(
% 0.20/0.54    r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))),
% 0.20/0.54    inference(resolution,[],[f209,f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f209,plain,(
% 0.20/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))),
% 0.20/0.54    inference(resolution,[],[f208,f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.54  fof(f208,plain,(
% 0.20/0.54    ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))),
% 0.20/0.54    inference(resolution,[],[f207,f30])).
% 0.20/0.54  fof(f207,plain,(
% 0.20/0.54    ~m1_subset_1(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k1_zfmisc_1(sK0)) | r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))),
% 0.20/0.54    inference(resolution,[],[f203,f24])).
% 0.20/0.54  fof(f203,plain,(
% 0.20/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k1_zfmisc_1(sK0)) | r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))),
% 0.20/0.54    inference(resolution,[],[f202,f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,k3_subset_1(X0,X2)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(nnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 0.20/0.54  fof(f202,plain,(
% 0.20/0.54    r1_xboole_0(sK1,k3_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,sK2))))),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f201])).
% 0.20/0.54  fof(f201,plain,(
% 0.20/0.54    sK1 != sK1 | r1_xboole_0(sK1,k3_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,sK2))))),
% 0.20/0.54    inference(superposition,[],[f38,f198])).
% 0.20/0.54  fof(f198,plain,(
% 0.20/0.54    sK1 = k4_xboole_0(sK1,k3_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,sK2))))),
% 0.20/0.54    inference(resolution,[],[f196,f24])).
% 0.20/0.54  fof(f196,plain,(
% 0.20/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | sK1 = k4_xboole_0(sK1,k3_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,sK2))))),
% 0.20/0.54    inference(resolution,[],[f158,f66])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    sK1 != sK1 | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.54    inference(superposition,[],[f38,f62])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    sK1 = k4_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.54    inference(resolution,[],[f61,f24])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | sK1 = k4_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.54    inference(resolution,[],[f58,f25])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)) | sK1 = k4_xboole_0(sK1,k3_subset_1(X0,sK2))) )),
% 0.20/0.54    inference(resolution,[],[f50,f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    r1_tarski(sK1,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X4,X5,X3] : (~r1_tarski(X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(X5)) | ~m1_subset_1(X3,k1_zfmisc_1(X5)) | k4_xboole_0(X3,k3_subset_1(X5,X4)) = X3) )),
% 0.20/0.54    inference(resolution,[],[f36,f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f158,plain,(
% 0.20/0.54    ( ! [X1] : (~r1_xboole_0(X1,k3_subset_1(sK0,sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | k4_xboole_0(X1,k3_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))) = X1) )),
% 0.20/0.54    inference(resolution,[],[f108,f25])).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(X4)) | ~r1_xboole_0(X3,k3_subset_1(X4,X5)) | ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k4_xboole_0(X3,k3_subset_1(X4,k3_subset_1(X4,k3_subset_1(X4,X5)))) = X3) )),
% 0.20/0.54    inference(resolution,[],[f102,f30])).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | k4_xboole_0(X0,k3_subset_1(X1,k3_subset_1(X1,X2))) = X0 | ~r1_xboole_0(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f101])).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k4_xboole_0(X0,k3_subset_1(X1,k3_subset_1(X1,X2))) = X0 | ~r1_xboole_0(X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(resolution,[],[f59,f30])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X4,X2,X3,X1] : (~m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | k4_xboole_0(X4,k3_subset_1(X3,k3_subset_1(X1,X2))) = X4 | ~r1_xboole_0(X4,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(resolution,[],[f50,f31])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f265,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,k3_subset_1(sK0,k3_subset_1(sK0,sK2))) | r1_xboole_0(X0,sK3)) )),
% 0.20/0.54    inference(superposition,[],[f40,f264])).
% 0.20/0.54  fof(f264,plain,(
% 0.20/0.54    k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),sK3)),
% 0.20/0.54    inference(resolution,[],[f263,f26])).
% 0.20/0.54  fof(f263,plain,(
% 0.20/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),sK3)),
% 0.20/0.54    inference(resolution,[],[f237,f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    r1_xboole_0(sK3,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f237,plain,(
% 0.20/0.54    ( ! [X1] : (~r1_xboole_0(X1,sK2) | k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) )),
% 0.20/0.54    inference(resolution,[],[f193,f25])).
% 0.20/0.54  fof(f193,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | k3_subset_1(X1,k3_subset_1(X1,X2)) = k4_xboole_0(k3_subset_1(X1,k3_subset_1(X1,X2)),X0) | ~r1_xboole_0(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f192])).
% 0.20/0.54  fof(f192,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k3_subset_1(X1,k3_subset_1(X1,X2)) = k4_xboole_0(k3_subset_1(X1,k3_subset_1(X1,X2)),X0) | ~r1_xboole_0(X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(resolution,[],[f74,f30])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    ( ! [X4,X2,X3,X1] : (~m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | k3_subset_1(X3,k3_subset_1(X1,X2)) = k4_xboole_0(k3_subset_1(X3,k3_subset_1(X1,X2)),X4) | ~r1_xboole_0(X4,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(resolution,[],[f71,f31])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k3_subset_1(X1,X2) = k4_xboole_0(k3_subset_1(X1,X2),X0)) )),
% 0.20/0.54    inference(resolution,[],[f70,f37])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(k3_subset_1(X1,X0),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X2,X0)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f69])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | r1_xboole_0(k3_subset_1(X1,X0),X2) | ~r1_tarski(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(resolution,[],[f53,f30])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | r1_xboole_0(k3_subset_1(X2,X1),X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | r1_xboole_0(k3_subset_1(X2,X1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))) )),
% 0.20/0.54    inference(resolution,[],[f33,f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(nnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (25265)------------------------------
% 0.20/0.54  % (25265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25265)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (25265)Memory used [KB]: 1791
% 0.20/0.54  % (25265)Time elapsed: 0.120 s
% 0.20/0.54  % (25265)------------------------------
% 0.20/0.54  % (25265)------------------------------
% 0.20/0.54  % (25255)Success in time 0.181 s
%------------------------------------------------------------------------------
