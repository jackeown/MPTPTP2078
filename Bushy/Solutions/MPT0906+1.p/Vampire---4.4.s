%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t66_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:12 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  60 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 240 expanded)
%              Number of equality atoms :   79 ( 191 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(subsumption_resolution,[],[f53,f40])).

fof(f40,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t66_mcart_1.p',t113_zfmisc_1)).

fof(f53,plain,(
    k2_zfmisc_1(k1_xboole_0,sK1) != k1_xboole_0 ),
    inference(backward_demodulation,[],[f52,f30])).

fof(f30,plain,(
    k2_zfmisc_1(sK0,sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( k2_mcart_1(sK2) = sK2
      | k1_mcart_1(sK2) = sK2 )
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k2_zfmisc_1(sK0,sK1) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k2_mcart_1(X2) = X2
              | k1_mcart_1(X2) = X2 )
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k2_zfmisc_1(X0,X1) != k1_xboole_0 )
   => ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k2_zfmisc_1(sK0,sK1) != k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
     => ( ( k2_mcart_1(sK2) = sK2
          | k1_mcart_1(sK2) = sK2 )
        & m1_subset_1(sK2,k2_zfmisc_1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k1_xboole_0
       => ! [X2] :
            ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
           => ( k2_mcart_1(X2) != X2
              & k1_mcart_1(X2) != X2 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t66_mcart_1.p',t66_mcart_1)).

fof(f52,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f50,f39])).

fof(f39,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,
    ( k2_zfmisc_1(sK0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f30,f48])).

fof(f48,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f47,f41])).

fof(f41,plain,
    ( k1_mcart_1(sK2) != sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f31,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t66_mcart_1.p',t26_mcart_1)).

fof(f31,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_mcart_1(sK2) = sK2 ),
    inference(trivial_inequality_removal,[],[f46])).

fof(f46,plain,
    ( sK2 != sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_mcart_1(sK2) = sK2 ),
    inference(superposition,[],[f42,f32])).

fof(f32,plain,
    ( k2_mcart_1(sK2) = sK2
    | k1_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,
    ( k2_mcart_1(sK2) != sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f31,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
