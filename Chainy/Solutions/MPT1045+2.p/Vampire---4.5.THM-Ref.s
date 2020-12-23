%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1045+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:04 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 164 expanded)
%              Number of leaves         :    7 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  165 ( 855 expanded)
%              Number of equality atoms :   54 ( 386 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5375,plain,(
    $false ),
    inference(global_subsumption,[],[f5333,f5371,f5374])).

fof(f5374,plain,
    ( ~ v1_partfun1(sK162,k1_xboole_0)
    | k1_xboole_0 != sK161 ),
    inference(superposition,[],[f5369,f3431])).

fof(f3431,plain,
    ( k1_xboole_0 = sK160
    | k1_xboole_0 != sK161 ),
    inference(cnf_transformation,[],[f2726])).

fof(f2726,plain,
    ( k1_tarski(sK162) != k5_partfun1(sK160,sK161,k3_partfun1(sK162,sK160,sK161))
    & ( k1_xboole_0 = sK160
      | k1_xboole_0 != sK161 )
    & m1_subset_1(sK162,k1_zfmisc_1(k2_zfmisc_1(sK160,sK161)))
    & v1_funct_2(sK162,sK160,sK161)
    & v1_funct_1(sK162) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK160,sK161,sK162])],[f1630,f2725])).

fof(f2725,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(sK162) != k5_partfun1(sK160,sK161,k3_partfun1(sK162,sK160,sK161))
      & ( k1_xboole_0 = sK160
        | k1_xboole_0 != sK161 )
      & m1_subset_1(sK162,k1_zfmisc_1(k2_zfmisc_1(sK160,sK161)))
      & v1_funct_2(sK162,sK160,sK161)
      & v1_funct_1(sK162) ) ),
    introduced(choice_axiom,[])).

fof(f1630,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f1629])).

fof(f1629,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1553])).

fof(f1553,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1552])).

fof(f1552,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_funct_2)).

fof(f5369,plain,(
    ~ v1_partfun1(sK162,sK160) ),
    inference(subsumption_resolution,[],[f5368,f3428])).

fof(f3428,plain,(
    v1_funct_1(sK162) ),
    inference(cnf_transformation,[],[f2726])).

fof(f5368,plain,
    ( ~ v1_partfun1(sK162,sK160)
    | ~ v1_funct_1(sK162) ),
    inference(subsumption_resolution,[],[f5367,f3430])).

fof(f3430,plain,(
    m1_subset_1(sK162,k1_zfmisc_1(k2_zfmisc_1(sK160,sK161))) ),
    inference(cnf_transformation,[],[f2726])).

fof(f5367,plain,
    ( ~ v1_partfun1(sK162,sK160)
    | ~ m1_subset_1(sK162,k1_zfmisc_1(k2_zfmisc_1(sK160,sK161)))
    | ~ v1_funct_1(sK162) ),
    inference(trivial_inequality_removal,[],[f5365])).

fof(f5365,plain,
    ( k1_tarski(sK162) != k1_tarski(sK162)
    | ~ v1_partfun1(sK162,sK160)
    | ~ m1_subset_1(sK162,k1_zfmisc_1(k2_zfmisc_1(sK160,sK161)))
    | ~ v1_funct_1(sK162) ),
    inference(superposition,[],[f5343,f3452])).

fof(f3452,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) = k5_partfun1(X0,X1,X2)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2739])).

fof(f2739,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_partfun1(X2,X0)
          | k1_tarski(X2) != k5_partfun1(X0,X1,X2) )
        & ( k1_tarski(X2) = k5_partfun1(X0,X1,X2)
          | ~ v1_partfun1(X2,X0) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f1638])).

fof(f1638,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1637])).

fof(f1637,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1556])).

fof(f1556,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
      <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_partfun1)).

fof(f5343,plain,(
    k1_tarski(sK162) != k5_partfun1(sK160,sK161,sK162) ),
    inference(backward_demodulation,[],[f3432,f5275])).

fof(f5275,plain,(
    sK162 = k3_partfun1(sK162,sK160,sK161) ),
    inference(subsumption_resolution,[],[f5215,f3428])).

fof(f5215,plain,
    ( sK162 = k3_partfun1(sK162,sK160,sK161)
    | ~ v1_funct_1(sK162) ),
    inference(resolution,[],[f3430,f3461])).

fof(f3461,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_partfun1(X2,X0,X1) = X2
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1650])).

fof(f1650,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1649])).

fof(f1649,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1613])).

fof(f1613,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).

fof(f3432,plain,(
    k1_tarski(sK162) != k5_partfun1(sK160,sK161,k3_partfun1(sK162,sK160,sK161)) ),
    inference(cnf_transformation,[],[f2726])).

fof(f5371,plain,(
    k1_xboole_0 = sK161 ),
    inference(resolution,[],[f5369,f5307])).

fof(f5307,plain,
    ( v1_partfun1(sK162,sK160)
    | k1_xboole_0 = sK161 ),
    inference(subsumption_resolution,[],[f5306,f3428])).

fof(f5306,plain,
    ( k1_xboole_0 = sK161
    | v1_partfun1(sK162,sK160)
    | ~ v1_funct_1(sK162) ),
    inference(subsumption_resolution,[],[f5255,f3429])).

fof(f3429,plain,(
    v1_funct_2(sK162,sK160,sK161) ),
    inference(cnf_transformation,[],[f2726])).

fof(f5255,plain,
    ( k1_xboole_0 = sK161
    | v1_partfun1(sK162,sK160)
    | ~ v1_funct_2(sK162,sK160,sK161)
    | ~ v1_funct_1(sK162) ),
    inference(resolution,[],[f3430,f5207])).

fof(f5207,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f3685])).

fof(f3685,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1779])).

fof(f1779,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1778])).

fof(f1778,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1532])).

fof(f1532,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f5333,plain,
    ( v1_partfun1(sK162,k1_xboole_0)
    | k1_xboole_0 != sK161 ),
    inference(global_subsumption,[],[f5320])).

fof(f5320,plain,
    ( v1_partfun1(sK162,k1_xboole_0)
    | k1_xboole_0 != sK161 ),
    inference(subsumption_resolution,[],[f5319,f3833])).

fof(f3833,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f5319,plain,
    ( v1_partfun1(sK162,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK161 ),
    inference(superposition,[],[f5231,f3431])).

fof(f5231,plain,
    ( v1_partfun1(sK162,sK160)
    | ~ v1_xboole_0(sK160) ),
    inference(resolution,[],[f3430,f3694])).

fof(f3694,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1786])).

fof(f1786,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1469])).

fof(f1469,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
%------------------------------------------------------------------------------
