%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:45 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 568 expanded)
%              Number of leaves         :   16 ( 135 expanded)
%              Depth                    :   23
%              Number of atoms          :  241 (1810 expanded)
%              Number of equality atoms :   74 ( 378 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f358,plain,(
    $false ),
    inference(subsumption_resolution,[],[f357,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f357,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f115,f351])).

fof(f351,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f350,f56])).

fof(f350,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k9_relat_1(sK3,X0))
      | k1_xboole_0 = k9_relat_1(sK3,X0) ) ),
    inference(forward_demodulation,[],[f338,f328])).

fof(f328,plain,(
    k1_xboole_0 = k2_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f309])).

fof(f309,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f99,f307])).

fof(f307,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f302,f211])).

fof(f211,plain,(
    ! [X19] : r1_tarski(k9_relat_1(sK3,X19),k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f210,f103])).

fof(f103,plain,(
    ! [X3] : k2_relat_1(k7_relat_1(sK3,X3)) = k9_relat_1(sK3,X3) ),
    inference(resolution,[],[f66,f91])).

fof(f91,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f90,f63])).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f90,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) ),
    inference(resolution,[],[f62,f53])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f210,plain,(
    ! [X19] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X19)),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f205,f92])).

fof(f92,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK3,X0),sK3) ),
    inference(resolution,[],[f91,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f205,plain,(
    ! [X19] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X19)),k2_relat_1(sK3))
      | ~ r1_tarski(k7_relat_1(sK3,X19),sK3) ) ),
    inference(resolution,[],[f183,f113])).

fof(f113,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | r1_tarski(k2_relat_1(X3),k2_relat_1(sK3))
      | ~ r1_tarski(X3,sK3) ) ),
    inference(resolution,[],[f61,f91])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f183,plain,(
    ! [X5] : v1_relat_1(k7_relat_1(sK3,X5)) ),
    inference(subsumption_resolution,[],[f181,f63])).

fof(f181,plain,(
    ! [X5] :
      ( v1_relat_1(k7_relat_1(sK3,X5))
      | ~ v1_relat_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) ) ),
    inference(resolution,[],[f120,f62])).

fof(f120,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(resolution,[],[f117,f92])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ) ),
    inference(resolution,[],[f81,f53])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

fof(f302,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f115,f256])).

fof(f256,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(equality_resolution,[],[f188])).

fof(f188,plain,(
    ! [X1] :
      ( k1_tarski(X1) != k1_tarski(sK0)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X1))
      | k1_xboole_0 = k1_relat_1(sK3) ) ),
    inference(superposition,[],[f119,f123])).

fof(f123,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f105,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f105,plain,(
    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f104,f91])).

fof(f104,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f97,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f97,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(resolution,[],[f78,f53])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f119,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_relat_1(sK3)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f118,f91])).

fof(f118,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_relat_1(sK3)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f69,f52])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f99,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(resolution,[],[f58,f91])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f338,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(sK3,X0)
      | ~ r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0)) ) ),
    inference(backward_demodulation,[],[f260,f328])).

fof(f260,plain,(
    ! [X0] :
      ( k2_relat_1(sK3) = k9_relat_1(sK3,X0)
      | ~ r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f211,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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

fof(f115,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f55,f114])).

fof(f114,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) ),
    inference(resolution,[],[f80,f53])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f55,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (3555)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (3547)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.37/0.56  % (3555)Refutation not found, incomplete strategy% (3555)------------------------------
% 1.37/0.56  % (3555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (3555)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (3555)Memory used [KB]: 10746
% 1.37/0.56  % (3555)Time elapsed: 0.129 s
% 1.37/0.56  % (3555)------------------------------
% 1.37/0.56  % (3555)------------------------------
% 1.37/0.56  % (3551)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.61/0.57  % (3561)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.61/0.57  % (3549)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.61/0.57  % (3550)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.61/0.58  % (3556)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.61/0.58  % (3553)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.61/0.58  % (3562)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.61/0.58  % (3545)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.61/0.59  % (3570)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.61/0.59  % (3570)Refutation not found, incomplete strategy% (3570)------------------------------
% 1.61/0.59  % (3570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (3569)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.61/0.60  % (3570)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.60  
% 1.61/0.60  % (3570)Memory used [KB]: 10618
% 1.61/0.60  % (3570)Time elapsed: 0.159 s
% 1.61/0.60  % (3570)------------------------------
% 1.61/0.60  % (3570)------------------------------
% 1.61/0.60  % (3548)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.61/0.60  % (3546)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.61/0.60  % (3568)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.61/0.60  % (3552)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.61/0.60  % (3575)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.61/0.60  % (3559)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.61/0.60  % (3566)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.61/0.61  % (3571)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.61/0.61  % (3560)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.61/0.61  % (3572)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.61/0.61  % (3558)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.61/0.61  % (3557)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.61/0.62  % (3554)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.61/0.62  % (3575)Refutation not found, incomplete strategy% (3575)------------------------------
% 1.61/0.62  % (3575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.62  % (3575)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.62  
% 1.61/0.62  % (3575)Memory used [KB]: 1663
% 1.61/0.62  % (3575)Time elapsed: 0.181 s
% 1.61/0.62  % (3575)------------------------------
% 1.61/0.62  % (3575)------------------------------
% 1.61/0.62  % (3567)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.61/0.62  % (3564)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.61/0.63  % (3574)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.61/0.63  % (3574)Refutation not found, incomplete strategy% (3574)------------------------------
% 1.61/0.63  % (3574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.63  % (3574)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.63  
% 1.61/0.63  % (3574)Memory used [KB]: 10746
% 1.61/0.63  % (3574)Time elapsed: 0.208 s
% 1.61/0.63  % (3574)------------------------------
% 1.61/0.63  % (3574)------------------------------
% 1.61/0.64  % (3565)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.61/0.64  % (3564)Refutation not found, incomplete strategy% (3564)------------------------------
% 1.61/0.64  % (3564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.64  % (3564)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.64  
% 1.61/0.64  % (3564)Memory used [KB]: 1663
% 1.61/0.64  % (3564)Time elapsed: 0.209 s
% 1.61/0.64  % (3564)------------------------------
% 1.61/0.64  % (3564)------------------------------
% 1.61/0.64  % (3573)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.61/0.65  % (3573)Refutation not found, incomplete strategy% (3573)------------------------------
% 1.61/0.65  % (3573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.65  % (3573)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.65  
% 1.61/0.65  % (3573)Memory used [KB]: 6268
% 1.61/0.65  % (3573)Time elapsed: 0.217 s
% 1.61/0.65  % (3573)------------------------------
% 1.61/0.65  % (3573)------------------------------
% 2.21/0.65  % (3552)Refutation found. Thanks to Tanya!
% 2.21/0.65  % SZS status Theorem for theBenchmark
% 2.21/0.65  % SZS output start Proof for theBenchmark
% 2.21/0.65  fof(f358,plain,(
% 2.21/0.65    $false),
% 2.21/0.65    inference(subsumption_resolution,[],[f357,f56])).
% 2.21/0.65  fof(f56,plain,(
% 2.21/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f2])).
% 2.21/0.65  fof(f2,axiom,(
% 2.21/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.21/0.65  fof(f357,plain,(
% 2.21/0.65    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.21/0.65    inference(backward_demodulation,[],[f115,f351])).
% 2.21/0.65  fof(f351,plain,(
% 2.21/0.65    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK3,X0)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f350,f56])).
% 2.21/0.65  fof(f350,plain,(
% 2.21/0.65    ( ! [X0] : (~r1_tarski(k1_xboole_0,k9_relat_1(sK3,X0)) | k1_xboole_0 = k9_relat_1(sK3,X0)) )),
% 2.21/0.65    inference(forward_demodulation,[],[f338,f328])).
% 2.21/0.65  fof(f328,plain,(
% 2.21/0.65    k1_xboole_0 = k2_relat_1(sK3)),
% 2.21/0.65    inference(trivial_inequality_removal,[],[f309])).
% 2.21/0.65  fof(f309,plain,(
% 2.21/0.65    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK3)),
% 2.21/0.65    inference(backward_demodulation,[],[f99,f307])).
% 2.21/0.65  fof(f307,plain,(
% 2.21/0.65    k1_xboole_0 = k1_relat_1(sK3)),
% 2.21/0.65    inference(subsumption_resolution,[],[f302,f211])).
% 2.21/0.65  fof(f211,plain,(
% 2.21/0.65    ( ! [X19] : (r1_tarski(k9_relat_1(sK3,X19),k2_relat_1(sK3))) )),
% 2.21/0.65    inference(forward_demodulation,[],[f210,f103])).
% 2.21/0.65  fof(f103,plain,(
% 2.21/0.65    ( ! [X3] : (k2_relat_1(k7_relat_1(sK3,X3)) = k9_relat_1(sK3,X3)) )),
% 2.21/0.65    inference(resolution,[],[f66,f91])).
% 2.21/0.65  fof(f91,plain,(
% 2.21/0.65    v1_relat_1(sK3)),
% 2.21/0.65    inference(subsumption_resolution,[],[f90,f63])).
% 2.21/0.65  fof(f63,plain,(
% 2.21/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f13])).
% 2.21/0.65  fof(f13,axiom,(
% 2.21/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.21/0.65  fof(f90,plain,(
% 2.21/0.65    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(k1_tarski(sK0),sK1))),
% 2.21/0.65    inference(resolution,[],[f62,f53])).
% 2.21/0.65  fof(f53,plain,(
% 2.21/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.21/0.65    inference(cnf_transformation,[],[f45])).
% 2.21/0.65  fof(f45,plain,(
% 2.21/0.65    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.21/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f44])).
% 2.21/0.65  fof(f44,plain,(
% 2.21/0.65    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.21/0.65    introduced(choice_axiom,[])).
% 2.21/0.65  fof(f28,plain,(
% 2.21/0.65    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.21/0.65    inference(flattening,[],[f27])).
% 2.21/0.65  fof(f27,plain,(
% 2.21/0.65    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.21/0.65    inference(ennf_transformation,[],[f25])).
% 2.21/0.65  fof(f25,plain,(
% 2.21/0.65    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.21/0.65    inference(pure_predicate_removal,[],[f24])).
% 2.21/0.65  fof(f24,negated_conjecture,(
% 2.21/0.65    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.21/0.65    inference(negated_conjecture,[],[f23])).
% 2.21/0.65  fof(f23,conjecture,(
% 2.21/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 2.21/0.65  fof(f62,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f32])).
% 2.21/0.65  fof(f32,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.21/0.65    inference(ennf_transformation,[],[f11])).
% 2.21/0.65  fof(f11,axiom,(
% 2.21/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.21/0.65  fof(f66,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f34])).
% 2.21/0.65  fof(f34,plain,(
% 2.21/0.65    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.21/0.65    inference(ennf_transformation,[],[f14])).
% 2.21/0.65  fof(f14,axiom,(
% 2.21/0.65    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 2.21/0.65  fof(f210,plain,(
% 2.21/0.65    ( ! [X19] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X19)),k2_relat_1(sK3))) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f205,f92])).
% 2.21/0.65  fof(f92,plain,(
% 2.21/0.65    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),sK3)) )),
% 2.21/0.65    inference(resolution,[],[f91,f65])).
% 2.21/0.65  fof(f65,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f33])).
% 2.21/0.65  fof(f33,plain,(
% 2.21/0.65    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.21/0.65    inference(ennf_transformation,[],[f18])).
% 2.21/0.65  fof(f18,axiom,(
% 2.21/0.65    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 2.21/0.65  fof(f205,plain,(
% 2.21/0.65    ( ! [X19] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X19)),k2_relat_1(sK3)) | ~r1_tarski(k7_relat_1(sK3,X19),sK3)) )),
% 2.21/0.65    inference(resolution,[],[f183,f113])).
% 2.21/0.65  fof(f113,plain,(
% 2.21/0.65    ( ! [X3] : (~v1_relat_1(X3) | r1_tarski(k2_relat_1(X3),k2_relat_1(sK3)) | ~r1_tarski(X3,sK3)) )),
% 2.21/0.65    inference(resolution,[],[f61,f91])).
% 2.21/0.65  fof(f61,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f31])).
% 2.21/0.65  fof(f31,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.21/0.65    inference(flattening,[],[f30])).
% 2.21/0.65  fof(f30,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.21/0.65    inference(ennf_transformation,[],[f16])).
% 2.21/0.65  fof(f16,axiom,(
% 2.21/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 2.21/0.65  fof(f183,plain,(
% 2.21/0.65    ( ! [X5] : (v1_relat_1(k7_relat_1(sK3,X5))) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f181,f63])).
% 2.21/0.65  fof(f181,plain,(
% 2.21/0.65    ( ! [X5] : (v1_relat_1(k7_relat_1(sK3,X5)) | ~v1_relat_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) )),
% 2.21/0.65    inference(resolution,[],[f120,f62])).
% 2.21/0.65  fof(f120,plain,(
% 2.21/0.65    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))) )),
% 2.21/0.65    inference(resolution,[],[f117,f92])).
% 2.21/0.65  fof(f117,plain,(
% 2.21/0.65    ( ! [X0] : (~r1_tarski(X0,sK3) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))) )),
% 2.21/0.65    inference(resolution,[],[f81,f53])).
% 2.21/0.65  fof(f81,plain,(
% 2.21/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f43])).
% 2.21/0.65  fof(f43,plain,(
% 2.21/0.65    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 2.21/0.65    inference(flattening,[],[f42])).
% 2.21/0.65  fof(f42,plain,(
% 2.21/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 2.21/0.65    inference(ennf_transformation,[],[f22])).
% 2.21/0.65  fof(f22,axiom,(
% 2.21/0.65    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).
% 2.21/0.65  fof(f302,plain,(
% 2.21/0.65    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_xboole_0 = k1_relat_1(sK3)),
% 2.21/0.65    inference(superposition,[],[f115,f256])).
% 2.21/0.65  fof(f256,plain,(
% 2.21/0.65    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 2.21/0.65    inference(equality_resolution,[],[f188])).
% 2.21/0.65  fof(f188,plain,(
% 2.21/0.65    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK0) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X1)) | k1_xboole_0 = k1_relat_1(sK3)) )),
% 2.21/0.65    inference(superposition,[],[f119,f123])).
% 2.21/0.65  fof(f123,plain,(
% 2.21/0.65    k1_tarski(sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 2.21/0.65    inference(resolution,[],[f105,f74])).
% 2.21/0.65  fof(f74,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.21/0.65    inference(cnf_transformation,[],[f51])).
% 2.21/0.65  fof(f51,plain,(
% 2.21/0.65    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.21/0.65    inference(flattening,[],[f50])).
% 2.21/0.65  fof(f50,plain,(
% 2.21/0.65    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.21/0.65    inference(nnf_transformation,[],[f10])).
% 2.21/0.65  fof(f10,axiom,(
% 2.21/0.65    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.21/0.65  fof(f105,plain,(
% 2.21/0.65    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 2.21/0.65    inference(subsumption_resolution,[],[f104,f91])).
% 2.21/0.65  fof(f104,plain,(
% 2.21/0.65    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | ~v1_relat_1(sK3)),
% 2.21/0.65    inference(resolution,[],[f97,f67])).
% 2.21/0.65  fof(f67,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f47])).
% 2.21/0.65  fof(f47,plain,(
% 2.21/0.65    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.21/0.65    inference(nnf_transformation,[],[f35])).
% 2.21/0.65  fof(f35,plain,(
% 2.21/0.65    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.21/0.65    inference(ennf_transformation,[],[f12])).
% 2.21/0.65  fof(f12,axiom,(
% 2.21/0.65    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.21/0.65  fof(f97,plain,(
% 2.21/0.65    v4_relat_1(sK3,k1_tarski(sK0))),
% 2.21/0.65    inference(resolution,[],[f78,f53])).
% 2.21/0.65  fof(f78,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f40])).
% 2.21/0.65  fof(f40,plain,(
% 2.21/0.65    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.65    inference(ennf_transformation,[],[f26])).
% 2.21/0.65  fof(f26,plain,(
% 2.21/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.21/0.65    inference(pure_predicate_removal,[],[f20])).
% 2.21/0.65  fof(f20,axiom,(
% 2.21/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.21/0.65  fof(f119,plain,(
% 2.21/0.65    ( ! [X0] : (k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f118,f91])).
% 2.21/0.65  fof(f118,plain,(
% 2.21/0.65    ( ! [X0] : (k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) | ~v1_relat_1(sK3)) )),
% 2.21/0.65    inference(resolution,[],[f69,f52])).
% 2.21/0.65  fof(f52,plain,(
% 2.21/0.65    v1_funct_1(sK3)),
% 2.21/0.65    inference(cnf_transformation,[],[f45])).
% 2.21/0.65  fof(f69,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f37])).
% 2.21/0.65  fof(f37,plain,(
% 2.21/0.65    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.21/0.65    inference(flattening,[],[f36])).
% 2.21/0.65  fof(f36,plain,(
% 2.21/0.65    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.21/0.65    inference(ennf_transformation,[],[f19])).
% 2.21/0.65  fof(f19,axiom,(
% 2.21/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 2.21/0.65  fof(f99,plain,(
% 2.21/0.65    k1_xboole_0 != k1_relat_1(sK3) | k1_xboole_0 = k2_relat_1(sK3)),
% 2.21/0.65    inference(resolution,[],[f58,f91])).
% 2.21/0.65  fof(f58,plain,(
% 2.21/0.65    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f46])).
% 2.21/0.65  fof(f46,plain,(
% 2.21/0.65    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.21/0.65    inference(nnf_transformation,[],[f29])).
% 2.21/0.65  fof(f29,plain,(
% 2.21/0.65    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.21/0.65    inference(ennf_transformation,[],[f17])).
% 2.21/0.65  fof(f17,axiom,(
% 2.21/0.65    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 2.21/0.65  fof(f338,plain,(
% 2.21/0.65    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK3,X0) | ~r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0))) )),
% 2.21/0.65    inference(backward_demodulation,[],[f260,f328])).
% 2.21/0.65  fof(f260,plain,(
% 2.21/0.65    ( ! [X0] : (k2_relat_1(sK3) = k9_relat_1(sK3,X0) | ~r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0))) )),
% 2.21/0.65    inference(resolution,[],[f211,f73])).
% 2.21/0.65  fof(f73,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f49])).
% 2.21/0.65  fof(f49,plain,(
% 2.21/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.65    inference(flattening,[],[f48])).
% 2.21/0.65  fof(f48,plain,(
% 2.21/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.65    inference(nnf_transformation,[],[f1])).
% 2.21/0.65  fof(f1,axiom,(
% 2.21/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.21/0.65  fof(f115,plain,(
% 2.21/0.65    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.21/0.65    inference(backward_demodulation,[],[f55,f114])).
% 2.21/0.65  fof(f114,plain,(
% 2.21/0.65    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(k1_tarski(sK0),sK1,sK3,X0)) )),
% 2.21/0.65    inference(resolution,[],[f80,f53])).
% 2.21/0.65  fof(f80,plain,(
% 2.21/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f41])).
% 2.21/0.65  fof(f41,plain,(
% 2.21/0.65    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.65    inference(ennf_transformation,[],[f21])).
% 2.21/0.65  fof(f21,axiom,(
% 2.21/0.65    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 2.21/0.65  fof(f55,plain,(
% 2.21/0.65    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.21/0.65    inference(cnf_transformation,[],[f45])).
% 2.21/0.65  % SZS output end Proof for theBenchmark
% 2.21/0.65  % (3552)------------------------------
% 2.21/0.65  % (3552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.65  % (3552)Termination reason: Refutation
% 2.21/0.65  
% 2.21/0.65  % (3552)Memory used [KB]: 1918
% 2.21/0.65  % (3552)Time elapsed: 0.148 s
% 2.21/0.65  % (3552)------------------------------
% 2.21/0.65  % (3552)------------------------------
% 2.21/0.65  % (3544)Success in time 0.289 s
%------------------------------------------------------------------------------
