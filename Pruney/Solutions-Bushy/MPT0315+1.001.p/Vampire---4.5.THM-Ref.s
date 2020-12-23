%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0315+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  59 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 189 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36,plain,(
    $false ),
    inference(global_subsumption,[],[f15,f26,f35])).

fof(f35,plain,(
    ~ r1_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f32,f16])).

fof(f16,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    & ( r1_xboole_0(sK2,sK3)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        & ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) ) )
   => ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
      & ( r1_xboole_0(sK2,sK3)
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) )
       => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f29,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f7,f11])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
      | ~ r1_xboole_0(X2,X4) ) ),
    inference(resolution,[],[f21,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        & r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        & k4_tarski(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4)) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f8,f13])).

fof(f13,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
     => ( r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        & r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        & k4_tarski(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6] :
            ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X5,k3_xboole_0(X1,X3))
              & k4_tarski(X5,X6) = X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).

fof(f26,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f24,f16])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f23,f17])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
      | ~ r1_xboole_0(X1,X3) ) ),
    inference(resolution,[],[f20,f18])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,plain,
    ( r1_xboole_0(sK2,sK3)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
