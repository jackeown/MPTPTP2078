%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t26_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:06 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  74 expanded)
%              Number of leaves         :    5 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 320 expanded)
%              Number of equality atoms :   64 ( 255 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(subsumption_resolution,[],[f48,f43])).

fof(f43,plain,(
    k1_mcart_1(sK2) != sK2 ),
    inference(superposition,[],[f39,f42])).

fof(f42,plain,(
    k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) = sK2 ),
    inference(subsumption_resolution,[],[f41,f30])).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( k2_mcart_1(sK2) = sK2
      | k1_mcart_1(sK2) = sK2 )
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k2_mcart_1(X2) = X2
              | k1_mcart_1(X2) = X2 )
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
     => ( ( k2_mcart_1(sK2) = sK2
          | k1_mcart_1(sK2) = sK2 )
        & m1_subset_1(sK2,k2_zfmisc_1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => ( k2_mcart_1(X2) != X2
                  & k1_mcart_1(X2) != X2 ) )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t26_mcart_1.p',t26_mcart_1)).

fof(f41,plain,
    ( k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) = sK2
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f40,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,
    ( k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f32,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t26_mcart_1.p',t24_mcart_1)).

fof(f32,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X2,X1] : k1_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t26_mcart_1.p',t20_mcart_1)).

fof(f48,plain,(
    k1_mcart_1(sK2) = sK2 ),
    inference(trivial_inequality_removal,[],[f45])).

fof(f45,plain,
    ( sK2 != sK2
    | k1_mcart_1(sK2) = sK2 ),
    inference(superposition,[],[f44,f33])).

fof(f33,plain,
    ( k2_mcart_1(sK2) = sK2
    | k1_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    k2_mcart_1(sK2) != sK2 ),
    inference(superposition,[],[f38,f42])).

fof(f38,plain,(
    ! [X2,X1] : k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
