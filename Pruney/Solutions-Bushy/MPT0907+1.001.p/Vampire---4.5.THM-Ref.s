%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0907+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:52 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   34 (  71 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :   13
%              Number of atoms          :   74 ( 175 expanded)
%              Number of equality atoms :   42 (  98 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(subsumption_resolution,[],[f37,f16])).

fof(f16,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f37,plain,(
    ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f24,f35])).

fof(f35,plain,(
    o_0_0_xboole_0 = k2_zfmisc_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f34,f33])).

fof(f33,plain,(
    sK0 = k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f30,f16])).

fof(f30,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f24,f28])).

fof(f28,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | sK0 = k1_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f27])).

fof(f27,plain,
    ( sK0 != sK0
    | o_0_0_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | sK0 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f26,f15])).

fof(f15,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).

fof(f26,plain,
    ( sK0 != k2_mcart_1(sK0)
    | o_0_0_xboole_0 = k2_zfmisc_1(sK1,sK2) ),
    inference(resolution,[],[f22,f25])).

fof(f25,plain,(
    m1_subset_1(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f18,f14])).

fof(f14,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k2_mcart_1(X2) != X2
      | o_0_0_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f17])).

fof(f17,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

fof(f34,plain,
    ( sK0 != k1_mcart_1(sK0)
    | o_0_0_xboole_0 = k2_zfmisc_1(sK1,sK2) ),
    inference(resolution,[],[f23,f25])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_mcart_1(X2) != X2
      | o_0_0_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f19,f17])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f21,f14])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

%------------------------------------------------------------------------------
