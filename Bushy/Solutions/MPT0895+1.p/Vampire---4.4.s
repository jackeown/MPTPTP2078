%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t55_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:10 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 569 expanded)
%              Number of leaves         :    5 ( 127 expanded)
%              Depth                    :   28
%              Number of atoms          :  212 (3279 expanded)
%              Number of equality atoms :  211 (3278 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(subsumption_resolution,[],[f95,f49])).

fof(f49,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t55_mcart_1.p',t113_zfmisc_1)).

fof(f95,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f94,f52])).

fof(f52,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X1,X2) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t55_mcart_1.p',t35_mcart_1)).

fof(f94,plain,(
    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(k1_xboole_0,sK1,sK2),sK3) ),
    inference(subsumption_resolution,[],[f86,f81])).

fof(f81,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f80,f49])).

fof(f80,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f75,f51])).

fof(f51,plain,(
    ! [X2,X0] : k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X2) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,k1_xboole_0,sK2),sK3)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f63,f74])).

fof(f74,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f73,f49])).

fof(f73,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f68,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_zfmisc_1(X0,X1,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,k1_xboole_0),sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f63,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f64,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f63,f56])).

fof(f56,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f55,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f54])).

fof(f54,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f36,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t55_mcart_1.p',d4_zfmisc_1)).

fof(f34,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 )
    & ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | ( k1_xboole_0 != sK3
        & k1_xboole_0 != sK2
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 )
        & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X3
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) )
   => ( ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
        | k1_xboole_0 = sK3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
      & ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
        | ( k1_xboole_0 != sK3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <~> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
      <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t55_mcart_1.p',t55_mcart_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    inference(subsumption_resolution,[],[f62,f47])).

fof(f47,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    inference(definition_unfolding,[],[f30,f35])).

fof(f30,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f61,f46])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f31,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f59,f45])).

fof(f45,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f32,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f58])).

fof(f58,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f44,f56])).

fof(f44,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f33,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(k1_xboole_0,sK1,sK2),sK3)
    | k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f81,f47])).
%------------------------------------------------------------------------------
