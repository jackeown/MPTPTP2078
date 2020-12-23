%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:56 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :  144 (13076 expanded)
%              Number of leaves         :   21 (4260 expanded)
%              Depth                    :   28
%              Number of atoms          :  446 (97535 expanded)
%              Number of equality atoms :   79 (2303 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1627,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1626,f88])).

fof(f88,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f61,f59])).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f61,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1626,plain,(
    ~ v2_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1583,f1463])).

fof(f1463,plain,(
    k6_partfun1(k1_xboole_0) = k1_partfun1(sK1,k1_xboole_0,k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1308,f1318])).

fof(f1318,plain,(
    k6_partfun1(k1_xboole_0) = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f965,f1198])).

fof(f1198,plain,(
    k1_xboole_0 = sK2 ),
    inference(unit_resulting_resolution,[],[f109,f697,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f697,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f696,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f696,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f614,f584])).

fof(f584,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f583,f50])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f42,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f583,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f582,f51])).

fof(f51,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f582,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f581,f52])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f581,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f580,f53])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f580,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f579,f54])).

fof(f54,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f579,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f578,f55])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f578,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f577,f455])).

fof(f455,plain,(
    ~ v2_funct_1(sK2) ),
    inference(unit_resulting_resolution,[],[f451,f57])).

fof(f57,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f451,plain,(
    v2_funct_2(sK3,sK0) ),
    inference(backward_demodulation,[],[f182,f443])).

fof(f443,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f442,f381])).

fof(f381,plain,(
    r1_tarski(sK0,k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f350,f90])).

fof(f90,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f64,f59])).

fof(f64,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f350,plain,(
    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f168,f291])).

fof(f291,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f62,f159,f158,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f158,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(backward_demodulation,[],[f147,f139])).

fof(f139,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f50,f53,f52,f55,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f147,plain,(
    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f50,f53,f52,f55,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f159,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f56,f139])).

fof(f56,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f168,plain,(
    r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f109,f150,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f150,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f69,f55,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f442,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(sK0,k2_relat_1(sK3)) ),
    inference(resolution,[],[f186,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f186,plain,(
    r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f150,f136,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f136,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f55,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f182,plain,(
    v2_funct_2(sK3,k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f180,f173])).

fof(f173,plain,(
    v5_relat_1(sK3,k2_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f93,f150,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f180,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | v2_funct_2(sK3,k2_relat_1(sK3)) ),
    inference(resolution,[],[f150,f92])).

fof(f92,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | v2_funct_2(X1,k2_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f577,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f574,f88])).

fof(f574,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f81,f346])).

fof(f346,plain,(
    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(backward_demodulation,[],[f139,f291])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f614,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f238,f584])).

fof(f238,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f183,f78])).

fof(f183,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f109,f100,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f100,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f52,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f109,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f69,f52,f68])).

fof(f965,plain,(
    k6_partfun1(k1_xboole_0) = k5_relat_1(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f630,f865])).

fof(f865,plain,(
    k1_xboole_0 = sK3 ),
    inference(unit_resulting_resolution,[],[f150,f665,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f665,plain,(
    k1_xboole_0 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f443,f584])).

fof(f630,plain,(
    k5_relat_1(sK2,sK3) = k6_partfun1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f291,f584])).

fof(f1308,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_partfun1(sK1,k1_xboole_0,k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f944,f1198])).

fof(f944,plain,(
    k5_relat_1(k1_xboole_0,sK2) = k1_partfun1(sK1,k1_xboole_0,k1_xboole_0,sK1,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f596,f865])).

fof(f596,plain,(
    k5_relat_1(sK3,sK2) = k1_partfun1(sK1,k1_xboole_0,k1_xboole_0,sK1,sK3,sK2) ),
    inference(backward_demodulation,[],[f137,f584])).

fof(f137,plain,(
    k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f53,f50,f52,f55,f85])).

fof(f1583,plain,(
    ~ v2_funct_1(k1_partfun1(sK1,k1_xboole_0,k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f869,f869,f1225,f941,f942,f1242,f1243,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X3] :
      ( ~ v2_funct_1(k1_partfun1(X0,k1_xboole_0,k1_xboole_0,X2,X3,X4))
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | ~ v1_funct_2(X4,k1_xboole_0,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X3,X0,k1_xboole_0)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1243,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(backward_demodulation,[],[f586,f1198])).

fof(f586,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(backward_demodulation,[],[f52,f584])).

fof(f1242,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f585,f1198])).

fof(f585,plain,(
    v1_funct_2(sK2,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f51,f584])).

fof(f942,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f588,f865])).

fof(f588,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f55,f584])).

fof(f941,plain,(
    v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f587,f865])).

% (15296)Refutation not found, incomplete strategy% (15296)------------------------------
% (15296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15296)Termination reason: Refutation not found, incomplete strategy

% (15296)Memory used [KB]: 10874
% (15296)Time elapsed: 0.216 s
% (15296)------------------------------
% (15296)------------------------------
fof(f587,plain,(
    v1_funct_2(sK3,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f54,f584])).

fof(f1225,plain,(
    ~ v2_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f455,f1198])).

fof(f869,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f53,f865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 21:02:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (831291392)
% 0.13/0.37  ipcrm: permission denied for id (831356931)
% 0.13/0.37  ipcrm: permission denied for id (831389700)
% 0.13/0.37  ipcrm: permission denied for id (831422469)
% 0.13/0.37  ipcrm: permission denied for id (831455239)
% 0.13/0.38  ipcrm: permission denied for id (831520777)
% 0.13/0.38  ipcrm: permission denied for id (831586314)
% 0.13/0.38  ipcrm: permission denied for id (831619083)
% 0.13/0.38  ipcrm: permission denied for id (831684621)
% 0.13/0.39  ipcrm: permission denied for id (831881236)
% 0.13/0.39  ipcrm: permission denied for id (831914005)
% 0.13/0.40  ipcrm: permission denied for id (832077852)
% 0.13/0.40  ipcrm: permission denied for id (832110621)
% 0.13/0.40  ipcrm: permission denied for id (832143390)
% 0.13/0.41  ipcrm: permission denied for id (832274466)
% 0.13/0.41  ipcrm: permission denied for id (832307235)
% 0.22/0.42  ipcrm: permission denied for id (832438312)
% 0.22/0.42  ipcrm: permission denied for id (832471081)
% 0.22/0.42  ipcrm: permission denied for id (832503850)
% 0.22/0.42  ipcrm: permission denied for id (832634927)
% 0.22/0.43  ipcrm: permission denied for id (832831542)
% 0.22/0.43  ipcrm: permission denied for id (832864311)
% 0.22/0.45  ipcrm: permission denied for id (833224769)
% 0.22/0.45  ipcrm: permission denied for id (833257538)
% 0.22/0.46  ipcrm: permission denied for id (833454152)
% 0.22/0.46  ipcrm: permission denied for id (833552461)
% 0.22/0.47  ipcrm: permission denied for id (833617999)
% 0.22/0.47  ipcrm: permission denied for id (833650768)
% 0.22/0.47  ipcrm: permission denied for id (833716308)
% 0.22/0.48  ipcrm: permission denied for id (833749077)
% 0.22/0.48  ipcrm: permission denied for id (833814615)
% 0.22/0.48  ipcrm: permission denied for id (833847384)
% 0.22/0.48  ipcrm: permission denied for id (833912922)
% 0.22/0.49  ipcrm: permission denied for id (833978460)
% 0.22/0.49  ipcrm: permission denied for id (834011229)
% 0.22/0.50  ipcrm: permission denied for id (834240612)
% 0.22/0.51  ipcrm: permission denied for id (834338921)
% 0.22/0.51  ipcrm: permission denied for id (834371691)
% 0.22/0.51  ipcrm: permission denied for id (834502768)
% 0.22/0.51  ipcrm: permission denied for id (834535537)
% 0.22/0.52  ipcrm: permission denied for id (834568306)
% 0.22/0.52  ipcrm: permission denied for id (834601075)
% 0.22/0.52  ipcrm: permission denied for id (834633844)
% 0.22/0.52  ipcrm: permission denied for id (834666613)
% 0.22/0.52  ipcrm: permission denied for id (834732151)
% 0.22/0.52  ipcrm: permission denied for id (834797689)
% 0.22/0.52  ipcrm: permission denied for id (834830458)
% 0.22/0.53  ipcrm: permission denied for id (834863227)
% 0.22/0.53  ipcrm: permission denied for id (834994303)
% 1.11/0.71  % (15278)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.11/0.71  % (15294)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.11/0.71  % (15279)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.67/0.72  % (15295)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.67/0.72  % (15286)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.67/0.73  % (15278)Refutation not found, incomplete strategy% (15278)------------------------------
% 1.67/0.73  % (15278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.73  % (15287)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.67/0.74  % (15271)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.67/0.74  % (15278)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.74  
% 1.67/0.74  % (15278)Memory used [KB]: 10874
% 1.67/0.74  % (15278)Time elapsed: 0.121 s
% 1.67/0.74  % (15278)------------------------------
% 1.67/0.74  % (15278)------------------------------
% 2.00/0.77  % (15269)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 2.00/0.77  % (15270)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 2.00/0.77  % (15268)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 2.00/0.78  % (15289)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.00/0.78  % (15293)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.00/0.78  % (15291)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 2.00/0.78  % (15282)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 2.00/0.78  % (15292)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.00/0.78  % (15297)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 2.00/0.78  % (15285)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.00/0.78  % (15275)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 2.00/0.78  % (15290)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.00/0.78  % (15284)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 2.00/0.79  % (15284)Refutation not found, incomplete strategy% (15284)------------------------------
% 2.00/0.79  % (15284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.79  % (15284)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.79  
% 2.00/0.79  % (15284)Memory used [KB]: 10746
% 2.00/0.79  % (15284)Time elapsed: 0.177 s
% 2.00/0.79  % (15284)------------------------------
% 2.00/0.79  % (15284)------------------------------
% 2.00/0.79  % (15273)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 2.00/0.79  % (15283)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.00/0.79  % (15274)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.00/0.79  % (15277)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.00/0.79  % (15276)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 2.00/0.79  % (15281)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.00/0.80  % (15288)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.00/0.80  % (15272)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 2.00/0.82  % (15296)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.00/0.82  % (15280)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.00/0.83  % (15279)Refutation found. Thanks to Tanya!
% 2.00/0.83  % SZS status Theorem for theBenchmark
% 2.00/0.83  % SZS output start Proof for theBenchmark
% 2.00/0.83  fof(f1627,plain,(
% 2.00/0.83    $false),
% 2.00/0.83    inference(subsumption_resolution,[],[f1626,f88])).
% 2.00/0.83  fof(f88,plain,(
% 2.00/0.83    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.00/0.83    inference(definition_unfolding,[],[f61,f59])).
% 2.00/0.83  fof(f59,plain,(
% 2.00/0.83    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.00/0.83    inference(cnf_transformation,[],[f17])).
% 2.00/0.83  fof(f17,axiom,(
% 2.00/0.83    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.00/0.83  fof(f61,plain,(
% 2.00/0.83    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.00/0.83    inference(cnf_transformation,[],[f10])).
% 2.00/0.83  fof(f10,axiom,(
% 2.00/0.83    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.00/0.83  fof(f1626,plain,(
% 2.00/0.83    ~v2_funct_1(k6_partfun1(k1_xboole_0))),
% 2.00/0.83    inference(forward_demodulation,[],[f1583,f1463])).
% 2.00/0.83  fof(f1463,plain,(
% 2.00/0.83    k6_partfun1(k1_xboole_0) = k1_partfun1(sK1,k1_xboole_0,k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0)),
% 2.00/0.83    inference(backward_demodulation,[],[f1308,f1318])).
% 2.00/0.83  fof(f1318,plain,(
% 2.00/0.83    k6_partfun1(k1_xboole_0) = k5_relat_1(k1_xboole_0,k1_xboole_0)),
% 2.00/0.83    inference(backward_demodulation,[],[f965,f1198])).
% 2.00/0.83  fof(f1198,plain,(
% 2.00/0.83    k1_xboole_0 = sK2),
% 2.00/0.83    inference(unit_resulting_resolution,[],[f109,f697,f65])).
% 2.00/0.83  fof(f65,plain,(
% 2.00/0.83    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 2.00/0.83    inference(cnf_transformation,[],[f25])).
% 2.00/0.83  fof(f25,plain,(
% 2.00/0.83    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.00/0.83    inference(flattening,[],[f24])).
% 2.00/0.83  fof(f24,plain,(
% 2.00/0.83    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.00/0.83    inference(ennf_transformation,[],[f8])).
% 2.00/0.83  fof(f8,axiom,(
% 2.00/0.83    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 2.00/0.83  fof(f697,plain,(
% 2.00/0.83    k1_xboole_0 = k1_relat_1(sK2)),
% 2.00/0.83    inference(subsumption_resolution,[],[f696,f58])).
% 2.00/0.83  fof(f58,plain,(
% 2.00/0.83    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.00/0.83    inference(cnf_transformation,[],[f2])).
% 2.00/0.83  fof(f2,axiom,(
% 2.00/0.83    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.00/0.83  fof(f696,plain,(
% 2.00/0.83    ~r1_tarski(k1_xboole_0,k1_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2)),
% 2.00/0.83    inference(forward_demodulation,[],[f614,f584])).
% 2.00/0.83  fof(f584,plain,(
% 2.00/0.83    k1_xboole_0 = sK0),
% 2.00/0.83    inference(subsumption_resolution,[],[f583,f50])).
% 2.00/0.83  fof(f50,plain,(
% 2.00/0.83    v1_funct_1(sK2)),
% 2.00/0.83    inference(cnf_transformation,[],[f43])).
% 2.00/0.83  fof(f43,plain,(
% 2.00/0.83    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.00/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f42,f41])).
% 2.00/0.83  fof(f41,plain,(
% 2.00/0.83    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.00/0.83    introduced(choice_axiom,[])).
% 2.00/0.83  fof(f42,plain,(
% 2.00/0.83    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.00/0.83    introduced(choice_axiom,[])).
% 2.00/0.83  fof(f23,plain,(
% 2.00/0.83    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.00/0.83    inference(flattening,[],[f22])).
% 2.00/0.83  fof(f22,plain,(
% 2.00/0.83    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.00/0.83    inference(ennf_transformation,[],[f20])).
% 2.00/0.83  fof(f20,negated_conjecture,(
% 2.00/0.83    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.00/0.83    inference(negated_conjecture,[],[f19])).
% 2.00/0.83  fof(f19,conjecture,(
% 2.00/0.83    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 2.00/0.83  fof(f583,plain,(
% 2.00/0.83    k1_xboole_0 = sK0 | ~v1_funct_1(sK2)),
% 2.00/0.83    inference(subsumption_resolution,[],[f582,f51])).
% 2.00/0.83  fof(f51,plain,(
% 2.00/0.83    v1_funct_2(sK2,sK0,sK1)),
% 2.00/0.83    inference(cnf_transformation,[],[f43])).
% 2.00/0.83  fof(f582,plain,(
% 2.00/0.83    k1_xboole_0 = sK0 | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.00/0.83    inference(subsumption_resolution,[],[f581,f52])).
% 2.00/0.83  fof(f52,plain,(
% 2.00/0.83    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.00/0.83    inference(cnf_transformation,[],[f43])).
% 2.00/0.83  fof(f581,plain,(
% 2.00/0.83    k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.00/0.83    inference(subsumption_resolution,[],[f580,f53])).
% 2.00/0.83  fof(f53,plain,(
% 2.00/0.83    v1_funct_1(sK3)),
% 2.00/0.83    inference(cnf_transformation,[],[f43])).
% 2.00/0.83  fof(f580,plain,(
% 2.00/0.83    k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.00/0.83    inference(subsumption_resolution,[],[f579,f54])).
% 2.00/0.83  fof(f54,plain,(
% 2.00/0.83    v1_funct_2(sK3,sK1,sK0)),
% 2.00/0.83    inference(cnf_transformation,[],[f43])).
% 2.00/0.83  fof(f579,plain,(
% 2.00/0.83    k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.00/0.83    inference(subsumption_resolution,[],[f578,f55])).
% 2.00/0.83  fof(f55,plain,(
% 2.00/0.83    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.00/0.83    inference(cnf_transformation,[],[f43])).
% 2.00/0.83  fof(f578,plain,(
% 2.00/0.83    k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.00/0.83    inference(subsumption_resolution,[],[f577,f455])).
% 2.00/0.83  fof(f455,plain,(
% 2.00/0.83    ~v2_funct_1(sK2)),
% 2.00/0.83    inference(unit_resulting_resolution,[],[f451,f57])).
% 2.00/0.83  fof(f57,plain,(
% 2.00/0.83    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.00/0.83    inference(cnf_transformation,[],[f43])).
% 2.00/0.83  fof(f451,plain,(
% 2.00/0.83    v2_funct_2(sK3,sK0)),
% 2.00/0.83    inference(backward_demodulation,[],[f182,f443])).
% 2.00/0.83  fof(f443,plain,(
% 2.00/0.83    sK0 = k2_relat_1(sK3)),
% 2.00/0.83    inference(subsumption_resolution,[],[f442,f381])).
% 2.00/0.83  fof(f381,plain,(
% 2.00/0.83    r1_tarski(sK0,k2_relat_1(sK3))),
% 2.00/0.83    inference(forward_demodulation,[],[f350,f90])).
% 2.00/0.83  fof(f90,plain,(
% 2.00/0.83    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.00/0.83    inference(definition_unfolding,[],[f64,f59])).
% 2.00/0.83  fof(f64,plain,(
% 2.00/0.83    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.00/0.83    inference(cnf_transformation,[],[f9])).
% 2.00/0.83  fof(f9,axiom,(
% 2.00/0.83    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.00/0.83  fof(f350,plain,(
% 2.00/0.83    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3))),
% 2.00/0.83    inference(backward_demodulation,[],[f168,f291])).
% 2.00/0.83  fof(f291,plain,(
% 2.00/0.83    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.00/0.83    inference(unit_resulting_resolution,[],[f62,f159,f158,f83])).
% 2.00/0.83  fof(f83,plain,(
% 2.00/0.83    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.83    inference(cnf_transformation,[],[f49])).
% 2.00/0.83  fof(f49,plain,(
% 2.00/0.83    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.83    inference(nnf_transformation,[],[f36])).
% 2.00/0.83  fof(f36,plain,(
% 2.00/0.83    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.83    inference(flattening,[],[f35])).
% 2.00/0.83  fof(f35,plain,(
% 2.00/0.83    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.00/0.83    inference(ennf_transformation,[],[f12])).
% 2.00/0.83  fof(f12,axiom,(
% 2.00/0.83    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.00/0.83  fof(f158,plain,(
% 2.00/0.83    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.00/0.83    inference(backward_demodulation,[],[f147,f139])).
% 2.00/0.83  fof(f139,plain,(
% 2.00/0.83    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.00/0.83    inference(unit_resulting_resolution,[],[f50,f53,f52,f55,f85])).
% 2.00/0.83  fof(f85,plain,(
% 2.00/0.83    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.00/0.83    inference(cnf_transformation,[],[f38])).
% 2.00/0.83  fof(f38,plain,(
% 2.00/0.83    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.00/0.83    inference(flattening,[],[f37])).
% 2.00/0.83  fof(f37,plain,(
% 2.00/0.83    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.00/0.83    inference(ennf_transformation,[],[f16])).
% 2.00/0.83  fof(f16,axiom,(
% 2.00/0.83    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.00/0.84  fof(f147,plain,(
% 2.00/0.84    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.00/0.84    inference(unit_resulting_resolution,[],[f50,f53,f52,f55,f87])).
% 2.00/0.84  fof(f87,plain,(
% 2.00/0.84    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.00/0.84    inference(cnf_transformation,[],[f40])).
% 2.00/0.84  fof(f40,plain,(
% 2.00/0.84    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.00/0.84    inference(flattening,[],[f39])).
% 2.00/0.84  fof(f39,plain,(
% 2.00/0.84    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.00/0.84    inference(ennf_transformation,[],[f14])).
% 2.00/0.84  fof(f14,axiom,(
% 2.00/0.84    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.00/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.00/0.84  fof(f159,plain,(
% 2.00/0.84    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.00/0.84    inference(backward_demodulation,[],[f56,f139])).
% 2.00/0.84  fof(f56,plain,(
% 2.00/0.84    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.00/0.84    inference(cnf_transformation,[],[f43])).
% 2.00/0.84  fof(f62,plain,(
% 2.00/0.84    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.00/0.84    inference(cnf_transformation,[],[f21])).
% 2.00/0.84  fof(f21,plain,(
% 2.00/0.84    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.00/0.84    inference(pure_predicate_removal,[],[f15])).
% 2.00/0.84  fof(f15,axiom,(
% 2.00/0.84    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.00/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.00/0.84  fof(f168,plain,(
% 2.00/0.84    r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3))),
% 2.00/0.84    inference(unit_resulting_resolution,[],[f109,f150,f67])).
% 2.00/0.84  fof(f67,plain,(
% 2.00/0.84    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.00/0.84    inference(cnf_transformation,[],[f26])).
% 2.00/0.84  fof(f26,plain,(
% 2.00/0.84    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.00/0.84    inference(ennf_transformation,[],[f7])).
% 2.00/0.84  fof(f7,axiom,(
% 2.00/0.84    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.00/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 2.00/0.84  fof(f150,plain,(
% 2.00/0.84    v1_relat_1(sK3)),
% 2.00/0.84    inference(unit_resulting_resolution,[],[f69,f55,f68])).
% 2.00/0.84  fof(f68,plain,(
% 2.00/0.84    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 2.00/0.84    inference(cnf_transformation,[],[f27])).
% 2.00/0.84  fof(f27,plain,(
% 2.00/0.84    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.00/0.84    inference(ennf_transformation,[],[f3])).
% 2.00/0.84  fof(f3,axiom,(
% 2.00/0.84    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.00/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.00/0.84  fof(f69,plain,(
% 2.00/0.84    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.00/0.84    inference(cnf_transformation,[],[f6])).
% 2.00/0.84  fof(f6,axiom,(
% 2.00/0.84    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.00/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.00/0.84  fof(f442,plain,(
% 2.00/0.84    sK0 = k2_relat_1(sK3) | ~r1_tarski(sK0,k2_relat_1(sK3))),
% 2.00/0.84    inference(resolution,[],[f186,f78])).
% 2.00/0.84  fof(f78,plain,(
% 2.00/0.84    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.00/0.84    inference(cnf_transformation,[],[f48])).
% 2.00/0.84  fof(f48,plain,(
% 2.00/0.84    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.00/0.84    inference(flattening,[],[f47])).
% 2.00/0.84  fof(f47,plain,(
% 2.00/0.84    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.00/0.84    inference(nnf_transformation,[],[f1])).
% 2.00/0.84  fof(f1,axiom,(
% 2.00/0.84    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.00/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.00/0.84  fof(f186,plain,(
% 2.00/0.84    r1_tarski(k2_relat_1(sK3),sK0)),
% 2.00/0.84    inference(unit_resulting_resolution,[],[f150,f136,f72])).
% 2.00/0.84  fof(f72,plain,(
% 2.00/0.84    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 2.00/0.84    inference(cnf_transformation,[],[f45])).
% 2.00/0.84  fof(f45,plain,(
% 2.00/0.84    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.00/0.84    inference(nnf_transformation,[],[f29])).
% 2.00/0.84  fof(f29,plain,(
% 2.00/0.84    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.00/0.84    inference(ennf_transformation,[],[f5])).
% 2.00/0.84  fof(f5,axiom,(
% 2.00/0.84    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.00/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.00/0.84  fof(f136,plain,(
% 2.00/0.84    v5_relat_1(sK3,sK0)),
% 2.00/0.84    inference(unit_resulting_resolution,[],[f55,f80])).
% 2.00/0.84  fof(f80,plain,(
% 2.00/0.84    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.00/0.84    inference(cnf_transformation,[],[f32])).
% 2.00/0.84  fof(f32,plain,(
% 2.00/0.84    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.84    inference(ennf_transformation,[],[f11])).
% 2.00/0.84  fof(f11,axiom,(
% 2.00/0.84    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.00/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.00/0.84  fof(f182,plain,(
% 2.00/0.84    v2_funct_2(sK3,k2_relat_1(sK3))),
% 2.00/0.84    inference(subsumption_resolution,[],[f180,f173])).
% 2.00/0.84  fof(f173,plain,(
% 2.00/0.84    v5_relat_1(sK3,k2_relat_1(sK3))),
% 2.00/0.84    inference(unit_resulting_resolution,[],[f93,f150,f73])).
% 2.00/0.84  fof(f73,plain,(
% 2.00/0.84    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0)) )),
% 2.00/0.84    inference(cnf_transformation,[],[f45])).
% 2.00/0.84  fof(f93,plain,(
% 2.00/0.84    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.00/0.84    inference(equality_resolution,[],[f77])).
% 2.00/0.84  fof(f77,plain,(
% 2.00/0.84    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.00/0.84    inference(cnf_transformation,[],[f48])).
% 2.00/0.84  fof(f180,plain,(
% 2.00/0.84    ~v5_relat_1(sK3,k2_relat_1(sK3)) | v2_funct_2(sK3,k2_relat_1(sK3))),
% 2.00/0.84    inference(resolution,[],[f150,f92])).
% 2.00/0.84  fof(f92,plain,(
% 2.00/0.84    ( ! [X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,k2_relat_1(X1)) | v2_funct_2(X1,k2_relat_1(X1))) )),
% 2.00/0.84    inference(equality_resolution,[],[f75])).
% 2.00/0.84  fof(f75,plain,(
% 2.00/0.84    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.00/0.84    inference(cnf_transformation,[],[f46])).
% 2.00/0.84  fof(f46,plain,(
% 2.00/0.84    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.00/0.84    inference(nnf_transformation,[],[f31])).
% 2.00/0.84  fof(f31,plain,(
% 2.00/0.84    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.00/0.84    inference(flattening,[],[f30])).
% 2.00/0.84  fof(f30,plain,(
% 2.00/0.84    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.00/0.84    inference(ennf_transformation,[],[f13])).
% 2.00/0.84  fof(f13,axiom,(
% 2.00/0.84    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.00/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 2.00/0.84  fof(f577,plain,(
% 2.00/0.84    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.00/0.84    inference(subsumption_resolution,[],[f574,f88])).
% 2.00/0.84  fof(f574,plain,(
% 2.00/0.84    ~v2_funct_1(k6_partfun1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.00/0.84    inference(superposition,[],[f81,f346])).
% 2.00/0.84  fof(f346,plain,(
% 2.00/0.84    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 2.00/0.84    inference(backward_demodulation,[],[f139,f291])).
% 2.00/0.84  fof(f81,plain,(
% 2.00/0.84    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.00/0.84    inference(cnf_transformation,[],[f34])).
% 2.00/0.84  fof(f34,plain,(
% 2.00/0.84    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.00/0.84    inference(flattening,[],[f33])).
% 2.00/0.84  fof(f33,plain,(
% 2.00/0.84    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.00/0.84    inference(ennf_transformation,[],[f18])).
% 2.00/0.84  fof(f18,axiom,(
% 2.00/0.84    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.00/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 2.00/0.84  fof(f614,plain,(
% 2.00/0.84    k1_xboole_0 = k1_relat_1(sK2) | ~r1_tarski(sK0,k1_relat_1(sK2))),
% 2.00/0.84    inference(backward_demodulation,[],[f238,f584])).
% 2.00/0.84  fof(f238,plain,(
% 2.00/0.84    sK0 = k1_relat_1(sK2) | ~r1_tarski(sK0,k1_relat_1(sK2))),
% 2.00/0.84    inference(resolution,[],[f183,f78])).
% 2.00/0.84  fof(f183,plain,(
% 2.00/0.84    r1_tarski(k1_relat_1(sK2),sK0)),
% 2.00/0.84    inference(unit_resulting_resolution,[],[f109,f100,f70])).
% 2.00/0.84  fof(f70,plain,(
% 2.00/0.84    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0)) )),
% 2.00/0.84    inference(cnf_transformation,[],[f44])).
% 2.00/0.84  fof(f44,plain,(
% 2.00/0.84    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.00/0.84    inference(nnf_transformation,[],[f28])).
% 2.00/0.84  fof(f28,plain,(
% 2.00/0.84    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.00/0.84    inference(ennf_transformation,[],[f4])).
% 2.00/0.84  fof(f4,axiom,(
% 2.00/0.84    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.00/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.00/0.84  fof(f100,plain,(
% 2.00/0.84    v4_relat_1(sK2,sK0)),
% 2.00/0.84    inference(unit_resulting_resolution,[],[f52,f79])).
% 2.00/0.84  fof(f79,plain,(
% 2.00/0.84    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.00/0.84    inference(cnf_transformation,[],[f32])).
% 2.00/0.84  fof(f109,plain,(
% 2.00/0.84    v1_relat_1(sK2)),
% 2.00/0.84    inference(unit_resulting_resolution,[],[f69,f52,f68])).
% 2.00/0.84  fof(f965,plain,(
% 2.00/0.84    k6_partfun1(k1_xboole_0) = k5_relat_1(sK2,k1_xboole_0)),
% 2.00/0.84    inference(backward_demodulation,[],[f630,f865])).
% 2.00/0.84  fof(f865,plain,(
% 2.00/0.84    k1_xboole_0 = sK3),
% 2.00/0.84    inference(unit_resulting_resolution,[],[f150,f665,f66])).
% 2.00/0.84  fof(f66,plain,(
% 2.00/0.84    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 2.00/0.84    inference(cnf_transformation,[],[f25])).
% 2.00/0.84  fof(f665,plain,(
% 2.00/0.84    k1_xboole_0 = k2_relat_1(sK3)),
% 2.00/0.84    inference(backward_demodulation,[],[f443,f584])).
% 2.00/0.84  fof(f630,plain,(
% 2.00/0.84    k5_relat_1(sK2,sK3) = k6_partfun1(k1_xboole_0)),
% 2.00/0.84    inference(backward_demodulation,[],[f291,f584])).
% 2.00/0.84  fof(f1308,plain,(
% 2.00/0.84    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_partfun1(sK1,k1_xboole_0,k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0)),
% 2.00/0.84    inference(backward_demodulation,[],[f944,f1198])).
% 2.00/0.84  fof(f944,plain,(
% 2.00/0.84    k5_relat_1(k1_xboole_0,sK2) = k1_partfun1(sK1,k1_xboole_0,k1_xboole_0,sK1,k1_xboole_0,sK2)),
% 2.00/0.84    inference(backward_demodulation,[],[f596,f865])).
% 2.00/0.84  fof(f596,plain,(
% 2.00/0.84    k5_relat_1(sK3,sK2) = k1_partfun1(sK1,k1_xboole_0,k1_xboole_0,sK1,sK3,sK2)),
% 2.00/0.84    inference(backward_demodulation,[],[f137,f584])).
% 2.00/0.84  fof(f137,plain,(
% 2.00/0.84    k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)),
% 2.00/0.84    inference(unit_resulting_resolution,[],[f53,f50,f52,f55,f85])).
% 2.00/0.84  fof(f1583,plain,(
% 2.00/0.84    ~v2_funct_1(k1_partfun1(sK1,k1_xboole_0,k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0))),
% 2.00/0.84    inference(unit_resulting_resolution,[],[f869,f869,f1225,f941,f942,f1242,f1243,f95])).
% 2.00/0.84  fof(f95,plain,(
% 2.00/0.84    ( ! [X4,X2,X0,X3] : (~v2_funct_1(k1_partfun1(X0,k1_xboole_0,k1_xboole_0,X2,X3,X4)) | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | ~v1_funct_2(X4,k1_xboole_0,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X3,X0,k1_xboole_0) | ~v1_funct_1(X3)) )),
% 2.00/0.84    inference(equality_resolution,[],[f82])).
% 2.00/0.84  fof(f82,plain,(
% 2.00/0.84    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.00/0.84    inference(cnf_transformation,[],[f34])).
% 2.00/0.84  fof(f1243,plain,(
% 2.00/0.84    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 2.00/0.84    inference(backward_demodulation,[],[f586,f1198])).
% 2.00/0.84  fof(f586,plain,(
% 2.00/0.84    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 2.00/0.84    inference(backward_demodulation,[],[f52,f584])).
% 2.00/0.84  fof(f1242,plain,(
% 2.00/0.84    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 2.00/0.84    inference(backward_demodulation,[],[f585,f1198])).
% 2.00/0.84  fof(f585,plain,(
% 2.00/0.84    v1_funct_2(sK2,k1_xboole_0,sK1)),
% 2.00/0.84    inference(backward_demodulation,[],[f51,f584])).
% 2.00/0.84  fof(f942,plain,(
% 2.00/0.84    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 2.00/0.84    inference(backward_demodulation,[],[f588,f865])).
% 2.00/0.84  fof(f588,plain,(
% 2.00/0.84    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 2.00/0.84    inference(backward_demodulation,[],[f55,f584])).
% 2.00/0.84  fof(f941,plain,(
% 2.00/0.84    v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)),
% 2.00/0.84    inference(backward_demodulation,[],[f587,f865])).
% 2.00/0.84  % (15296)Refutation not found, incomplete strategy% (15296)------------------------------
% 2.00/0.84  % (15296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.84  % (15296)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.84  
% 2.00/0.84  % (15296)Memory used [KB]: 10874
% 2.00/0.84  % (15296)Time elapsed: 0.216 s
% 2.00/0.84  % (15296)------------------------------
% 2.00/0.84  % (15296)------------------------------
% 2.00/0.84  fof(f587,plain,(
% 2.00/0.84    v1_funct_2(sK3,sK1,k1_xboole_0)),
% 2.00/0.84    inference(backward_demodulation,[],[f54,f584])).
% 2.00/0.84  fof(f1225,plain,(
% 2.00/0.84    ~v2_funct_1(k1_xboole_0)),
% 2.00/0.84    inference(backward_demodulation,[],[f455,f1198])).
% 2.00/0.84  fof(f869,plain,(
% 2.00/0.84    v1_funct_1(k1_xboole_0)),
% 2.00/0.84    inference(backward_demodulation,[],[f53,f865])).
% 2.00/0.84  % SZS output end Proof for theBenchmark
% 2.00/0.84  % (15279)------------------------------
% 2.00/0.84  % (15279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.84  % (15279)Termination reason: Refutation
% 2.00/0.84  
% 2.00/0.84  % (15279)Memory used [KB]: 7164
% 2.00/0.84  % (15279)Time elapsed: 0.217 s
% 2.00/0.84  % (15279)------------------------------
% 2.00/0.84  % (15279)------------------------------
% 2.53/0.85  % (15100)Success in time 0.481 s
%------------------------------------------------------------------------------
