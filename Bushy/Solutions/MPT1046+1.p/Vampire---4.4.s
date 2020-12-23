%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t162_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:35 EDT 2019

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   27 ( 148 expanded)
%              Number of leaves         :    3 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :   84 ( 600 expanded)
%              Number of equality atoms :   29 ( 178 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(subsumption_resolution,[],[f83,f48])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f44])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t162_funct_2.p',t162_funct_2)).

fof(f83,plain,(
    ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f82,f76])).

fof(f76,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f74,f50])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f73,f48])).

fof(f73,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f72,f50])).

fof(f72,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f71,f51])).

fof(f51,plain,(
    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,
    ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f49,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t162_funct_2.p',t161_funct_2)).

fof(f49,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f78,f77])).

fof(f77,plain,(
    k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)) != k1_tarski(sK1) ),
    inference(backward_demodulation,[],[f74,f51])).

fof(f78,plain,
    ( k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)) = k1_tarski(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f75,f66])).

fof(f66,plain,(
    ! [X2,X1] :
      ( k5_partfun1(k1_xboole_0,X1,k3_partfun1(X2,k1_xboole_0,X1)) = k1_tarski(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f74,f49])).
%------------------------------------------------------------------------------
