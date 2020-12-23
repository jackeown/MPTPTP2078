%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0906+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  58 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 233 expanded)
%              Number of equality atoms :   72 ( 184 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3416,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3411,f3341])).

fof(f3341,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f2461])).

fof(f2461,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f2028])).

fof(f2028,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f2027])).

fof(f2027,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f3411,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK62) ),
    inference(backward_demodulation,[],[f2302,f3407])).

fof(f3407,plain,(
    k1_xboole_0 = sK61 ),
    inference(subsumption_resolution,[],[f3403,f3340])).

fof(f3340,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f2462])).

fof(f2462,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f2028])).

fof(f3403,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK61,k1_xboole_0)
    | k1_xboole_0 = sK61 ),
    inference(superposition,[],[f2302,f3397])).

fof(f3397,plain,
    ( k1_xboole_0 = sK62
    | k1_xboole_0 = sK61 ),
    inference(global_subsumption,[],[f2304,f3391,f3392])).

fof(f3392,plain,
    ( sK63 != k2_mcart_1(sK63)
    | k1_xboole_0 = sK62
    | k1_xboole_0 = sK61 ),
    inference(resolution,[],[f2303,f2325])).

fof(f2325,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k2_mcart_1(X2) != X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1399])).

fof(f1399,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1331])).

fof(f1331,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f2303,plain,(
    m1_subset_1(sK63,k2_zfmisc_1(sK61,sK62)) ),
    inference(cnf_transformation,[],[f1946])).

fof(f1946,plain,
    ( ( sK63 = k2_mcart_1(sK63)
      | sK63 = k1_mcart_1(sK63) )
    & m1_subset_1(sK63,k2_zfmisc_1(sK61,sK62))
    & k1_xboole_0 != k2_zfmisc_1(sK61,sK62) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK61,sK62,sK63])],[f1387,f1945,f1944])).

fof(f1944,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k2_mcart_1(X2) = X2
              | k1_mcart_1(X2) = X2 )
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1) )
   => ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(sK61,sK62)) )
      & k1_xboole_0 != k2_zfmisc_1(sK61,sK62) ) ),
    introduced(choice_axiom,[])).

fof(f1945,plain,
    ( ? [X2] :
        ( ( k2_mcart_1(X2) = X2
          | k1_mcart_1(X2) = X2 )
        & m1_subset_1(X2,k2_zfmisc_1(sK61,sK62)) )
   => ( ( sK63 = k2_mcart_1(sK63)
        | sK63 = k1_mcart_1(sK63) )
      & m1_subset_1(sK63,k2_zfmisc_1(sK61,sK62)) ) ),
    introduced(choice_axiom,[])).

fof(f1387,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1374])).

fof(f1374,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
       => ! [X2] :
            ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
           => ( k2_mcart_1(X2) != X2
              & k1_mcart_1(X2) != X2 ) ) ) ),
    inference(negated_conjecture,[],[f1373])).

fof(f1373,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_mcart_1)).

fof(f3391,plain,
    ( sK63 != k1_mcart_1(sK63)
    | k1_xboole_0 = sK62
    | k1_xboole_0 = sK61 ),
    inference(resolution,[],[f2303,f2324])).

fof(f2324,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_mcart_1(X2) != X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1399])).

fof(f2304,plain,
    ( sK63 = k2_mcart_1(sK63)
    | sK63 = k1_mcart_1(sK63) ),
    inference(cnf_transformation,[],[f1946])).

fof(f2302,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK61,sK62) ),
    inference(cnf_transformation,[],[f1946])).
%------------------------------------------------------------------------------
