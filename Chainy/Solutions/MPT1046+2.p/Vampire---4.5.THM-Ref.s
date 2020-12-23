%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1046+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:04 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   29 (  94 expanded)
%              Number of leaves         :    5 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 362 expanded)
%              Number of equality atoms :   20 (  88 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2741,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2730,f2712])).

fof(f2712,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(backward_demodulation,[],[f2669,f2655])).

fof(f2655,plain,(
    sK1 = k3_partfun1(sK1,sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f2093,f2095,f2122])).

fof(f2122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_partfun1(X2,X0,X1) = X2
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1643])).

fof(f1643,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1642])).

fof(f1642,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1614])).

fof(f1614,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

fof(f2095,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f1948])).

fof(f1948,plain,
    ( k1_tarski(sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1623,f1947])).

fof(f1947,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( k1_tarski(sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1623,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0))
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f1622])).

fof(f1622,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0))
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1554])).

fof(f1554,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => k1_tarski(X1) = k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) ) ),
    inference(negated_conjecture,[],[f1553])).

fof(f1553,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_tarski(X1) = k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_2)).

fof(f2093,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1948])).

fof(f2669,plain,(
    v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f2093,f2094,f2095,f2128])).

fof(f2128,plain,(
    ! [X0,X1] :
      ( v1_partfun1(k3_partfun1(X1,X0,X0),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f1649])).

fof(f1649,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(k3_partfun1(X1,X0,X0),X0)
        & v1_funct_1(k3_partfun1(X1,X0,X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f1648])).

fof(f1648,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(k3_partfun1(X1,X0,X0),X0)
        & v1_funct_1(k3_partfun1(X1,X0,X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1509])).

fof(f1509,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v1_partfun1(k3_partfun1(X1,X0,X0),X0)
        & v1_funct_1(k3_partfun1(X1,X0,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_2)).

fof(f2094,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f1948])).

fof(f2730,plain,(
    ~ v1_partfun1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f2093,f2095,f2713,f2114])).

fof(f2114,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) = k5_partfun1(X0,X1,X2)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1955])).

fof(f1955,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_partfun1(X2,X0)
          | k1_tarski(X2) != k5_partfun1(X0,X1,X2) )
        & ( k1_tarski(X2) = k5_partfun1(X0,X1,X2)
          | ~ v1_partfun1(X2,X0) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f1631])).

fof(f1631,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1630])).

fof(f1630,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1557])).

fof(f1557,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
      <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

fof(f2713,plain,(
    k1_tarski(sK1) != k5_partfun1(sK0,sK0,sK1) ),
    inference(backward_demodulation,[],[f2096,f2655])).

fof(f2096,plain,(
    k1_tarski(sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) ),
    inference(cnf_transformation,[],[f1948])).
%------------------------------------------------------------------------------
