%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:24 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 872 expanded)
%              Number of leaves         :   22 ( 247 expanded)
%              Depth                    :   28
%              Number of atoms          :  476 (5617 expanded)
%              Number of equality atoms :  138 ( 895 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f582,plain,(
    $false ),
    inference(subsumption_resolution,[],[f513,f103])).

fof(f103,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f54,f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & sK0 = k2_relset_1(sK0,sK0,sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & k2_relset_1(X0,X0,X1) = X0
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
          & sK0 = k2_relset_1(sK0,sK0,sK1)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
        & sK0 = k2_relset_1(sK0,sK0,sK1)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
      & sK0 = k2_relset_1(sK0,sK0,sK1)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_1(X2) )
           => ( ( k2_relset_1(X0,X0,X1) = X0
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( k2_relset_1(X0,X0,X1) = X0
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( k2_relset_1(X0,X0,X1) = X0
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_funct_2)).

fof(f513,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(backward_demodulation,[],[f89,f508])).

fof(f508,plain,(
    sK2 = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f507,f100])).

fof(f100,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f54,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f507,plain,
    ( sK2 = k6_relat_1(sK0)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f506,f53])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f506,plain,
    ( sK2 = k6_relat_1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f505,f390])).

fof(f390,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f326,f388])).

fof(f388,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(superposition,[],[f341,f123])).

fof(f123,plain,(
    sK2 = k3_xboole_0(sK2,k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f106,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f106,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f54,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f341,plain,(
    ! [X1] : k7_relat_1(sK2,X1) = k3_xboole_0(sK2,k2_zfmisc_1(X1,sK0)) ),
    inference(backward_demodulation,[],[f118,f338])).

fof(f338,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f337,f127])).

fof(f127,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(resolution,[],[f126,f75])).

fof(f126,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f125,f54])).

fof(f125,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f69,f104])).

fof(f104,plain,(
    k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f54,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f337,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(resolution,[],[f335,f63])).

fof(f63,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f335,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f334,f98])).

fof(f98,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(forward_demodulation,[],[f94,f56])).

fof(f56,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,(
    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(resolution,[],[f52,f60])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f334,plain,(
    r1_tarski(k2_relat_1(sK1),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f332,f261])).

fof(f261,plain,(
    sK1 = k5_relat_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f249,f186])).

fof(f186,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) ),
    inference(backward_demodulation,[],[f55,f185])).

fof(f185,plain,(
    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f181,f51])).

fof(f51,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f181,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f108,f52])).

fof(f108,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k1_partfun1(X4,X5,sK0,sK0,X6,sK2) = k5_relat_1(X6,sK2)
      | ~ v1_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f105,f53])).

fof(f105,plain,(
    ! [X6,X4,X5] :
      ( k1_partfun1(X4,X5,sK0,sK0,X6,sK2) = k5_relat_1(X6,sK2)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X6) ) ),
    inference(resolution,[],[f54,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f55,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f249,plain,
    ( sK1 = k5_relat_1(sK1,sK2)
    | ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) ),
    inference(resolution,[],[f201,f92])).

fof(f92,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | sK1 = X3
      | ~ r2_relset_1(sK0,sK0,X3,sK1) ) ),
    inference(resolution,[],[f52,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f201,plain,(
    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f200,f185])).

fof(f200,plain,(
    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f196,f51])).

fof(f196,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f107,f52])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f101,f53])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f54,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f332,plain,(
    r1_tarski(k2_relat_1(k5_relat_1(sK1,sK2)),k2_relat_1(sK2)) ),
    inference(resolution,[],[f117,f90])).

fof(f90,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f52,f74])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(k5_relat_1(X0,sK2)),k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f100,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f118,plain,(
    ! [X1] : k7_relat_1(sK2,X1) = k3_xboole_0(sK2,k2_zfmisc_1(X1,k2_relat_1(sK2))) ),
    inference(resolution,[],[f100,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

fof(f326,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f323,f100])).

fof(f323,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f291,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f291,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f290,f98])).

fof(f290,plain,(
    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f289,f100])).

fof(f289,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f288,f53])).

fof(f288,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f287,f90])).

fof(f287,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f286,f51])).

fof(f286,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f283])).

fof(f283,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f65,f261])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f505,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = k6_relat_1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f504])).

fof(f504,plain,
    ( sK1 != sK1
    | sK0 != k1_relat_1(sK2)
    | sK2 = k6_relat_1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f154,f261])).

fof(f154,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(sK1,X0)
      | k1_relat_1(X0) != sK0
      | k6_relat_1(sK0) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f153,f98])).

fof(f153,plain,(
    ! [X0] :
      ( sK0 != k2_relat_1(sK1)
      | k1_relat_1(X0) != sK0
      | sK1 != k5_relat_1(sK1,X0)
      | k6_relat_1(sK0) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f152,f67])).

fof(f67,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f152,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | sK1 != k5_relat_1(sK1,X0)
      | k6_relat_1(sK0) = X0
      | k2_relat_1(sK1) != k1_relat_1(k6_relat_1(sK0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f151,f67])).

fof(f151,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(sK1,X0)
      | k6_relat_1(sK0) = X0
      | k1_relat_1(X0) != k1_relat_1(k6_relat_1(sK0))
      | k2_relat_1(sK1) != k1_relat_1(k6_relat_1(sK0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f150,f90])).

fof(f150,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(sK1,X0)
      | k6_relat_1(sK0) = X0
      | k1_relat_1(X0) != k1_relat_1(k6_relat_1(sK0))
      | k2_relat_1(sK1) != k1_relat_1(k6_relat_1(sK0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f149,f51])).

fof(f149,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(sK1,X0)
      | k6_relat_1(sK0) = X0
      | k1_relat_1(X0) != k1_relat_1(k6_relat_1(sK0))
      | k2_relat_1(sK1) != k1_relat_1(k6_relat_1(sK0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f148,f80])).

fof(f80,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f148,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(sK1,X0)
      | k6_relat_1(sK0) = X0
      | k1_relat_1(X0) != k1_relat_1(k6_relat_1(sK0))
      | k2_relat_1(sK1) != k1_relat_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f139,f79])).

fof(f79,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f139,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(sK1,X0)
      | k6_relat_1(sK0) = X0
      | k1_relat_1(X0) != k1_relat_1(k6_relat_1(sK0))
      | k2_relat_1(sK1) != k1_relat_1(k6_relat_1(sK0))
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ v1_relat_1(k6_relat_1(sK0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f86,f114])).

fof(f114,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f111,f98])).

fof(f111,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(resolution,[],[f90,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f86,plain,(
    ! [X2,X3,X1] :
      ( k5_relat_1(X1,X2) != k5_relat_1(X1,X3)
      | X2 = X3
      | k1_relat_1(X2) != k1_relat_1(X3)
      | k2_relat_1(X1) != k1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | k5_relat_1(X1,X2) != k5_relat_1(X1,X3)
      | k1_relat_1(X3) != X0
      | k1_relat_1(X2) != X0
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X2 = X3
              | k5_relat_1(X1,X2) != k5_relat_1(X1,X3)
              | k1_relat_1(X3) != X0
              | k1_relat_1(X2) != X0
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X2 = X3
              | k5_relat_1(X1,X2) != k5_relat_1(X1,X3)
              | k1_relat_1(X3) != X0
              | k1_relat_1(X2) != X0
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                  & k1_relat_1(X3) = X0
                  & k1_relat_1(X2) = X0
                  & k2_relat_1(X1) = X0 )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_1)).

fof(f89,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f57,f58])).

fof(f58,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f57,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:36:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (14700)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.51  % (14687)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (14692)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (14691)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (14688)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (14710)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (14712)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.52  % (14702)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (14706)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (14695)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (14714)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (14704)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (14707)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (14693)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (14715)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.53  % (14689)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (14698)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (14690)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (14703)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (14699)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (14703)Refutation not found, incomplete strategy% (14703)------------------------------
% 0.22/0.54  % (14703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14703)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14703)Memory used [KB]: 10746
% 0.22/0.54  % (14703)Time elapsed: 0.130 s
% 0.22/0.54  % (14703)------------------------------
% 0.22/0.54  % (14703)------------------------------
% 0.22/0.54  % (14713)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (14705)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (14716)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (14696)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (14708)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (14711)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (14709)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (14701)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (14694)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.56  % (14697)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.62/0.58  % (14701)Refutation found. Thanks to Tanya!
% 1.62/0.58  % SZS status Theorem for theBenchmark
% 1.62/0.58  % SZS output start Proof for theBenchmark
% 1.62/0.58  fof(f582,plain,(
% 1.62/0.58    $false),
% 1.62/0.58    inference(subsumption_resolution,[],[f513,f103])).
% 1.62/0.58  fof(f103,plain,(
% 1.62/0.58    r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.62/0.58    inference(resolution,[],[f54,f88])).
% 1.62/0.58  fof(f88,plain,(
% 1.62/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.62/0.58    inference(duplicate_literal_removal,[],[f87])).
% 1.62/0.58  fof(f87,plain,(
% 1.62/0.58    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.58    inference(equality_resolution,[],[f71])).
% 1.62/0.58  fof(f71,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f49])).
% 1.62/0.58  fof(f49,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.58    inference(nnf_transformation,[],[f35])).
% 1.62/0.58  fof(f35,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.58    inference(flattening,[],[f34])).
% 1.62/0.58  fof(f34,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.62/0.58    inference(ennf_transformation,[],[f16])).
% 1.62/0.58  fof(f16,axiom,(
% 1.62/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.62/0.58  fof(f54,plain,(
% 1.62/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  fof(f46,plain,(
% 1.62/0.58    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & sK0 = k2_relset_1(sK0,sK0,sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1)),
% 1.62/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f45,f44])).
% 1.62/0.58  fof(f44,plain,(
% 1.62/0.58    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & sK0 = k2_relset_1(sK0,sK0,sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f45,plain,(
% 1.62/0.58    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & sK0 = k2_relset_1(sK0,sK0,sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & sK0 = k2_relset_1(sK0,sK0,sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK2))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f24,plain,(
% 1.62/0.58    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.62/0.58    inference(flattening,[],[f23])).
% 1.62/0.58  fof(f23,plain,(
% 1.62/0.58    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 1.62/0.58    inference(ennf_transformation,[],[f22])).
% 1.62/0.58  fof(f22,plain,(
% 1.62/0.58    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.62/0.58    inference(pure_predicate_removal,[],[f21])).
% 1.62/0.58  fof(f21,negated_conjecture,(
% 1.62/0.58    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.62/0.58    inference(negated_conjecture,[],[f20])).
% 1.62/0.58  fof(f20,conjecture,(
% 1.62/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_funct_2)).
% 1.62/0.58  fof(f513,plain,(
% 1.62/0.58    ~r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.62/0.58    inference(backward_demodulation,[],[f89,f508])).
% 1.62/0.58  fof(f508,plain,(
% 1.62/0.58    sK2 = k6_relat_1(sK0)),
% 1.62/0.58    inference(subsumption_resolution,[],[f507,f100])).
% 1.62/0.58  fof(f100,plain,(
% 1.62/0.58    v1_relat_1(sK2)),
% 1.62/0.58    inference(resolution,[],[f54,f74])).
% 1.62/0.58  fof(f74,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f38])).
% 1.62/0.58  fof(f38,plain,(
% 1.62/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.58    inference(ennf_transformation,[],[f13])).
% 1.62/0.58  fof(f13,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.62/0.58  fof(f507,plain,(
% 1.62/0.58    sK2 = k6_relat_1(sK0) | ~v1_relat_1(sK2)),
% 1.62/0.58    inference(subsumption_resolution,[],[f506,f53])).
% 1.62/0.58  fof(f53,plain,(
% 1.62/0.58    v1_funct_1(sK2)),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  fof(f506,plain,(
% 1.62/0.58    sK2 = k6_relat_1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.62/0.58    inference(subsumption_resolution,[],[f505,f390])).
% 1.62/0.58  fof(f390,plain,(
% 1.62/0.58    sK0 = k1_relat_1(sK2)),
% 1.62/0.58    inference(backward_demodulation,[],[f326,f388])).
% 1.62/0.58  fof(f388,plain,(
% 1.62/0.58    sK2 = k7_relat_1(sK2,sK0)),
% 1.62/0.58    inference(superposition,[],[f341,f123])).
% 1.62/0.58  fof(f123,plain,(
% 1.62/0.58    sK2 = k3_xboole_0(sK2,k2_zfmisc_1(sK0,sK0))),
% 1.62/0.58    inference(resolution,[],[f106,f82])).
% 1.62/0.58  fof(f82,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.62/0.58    inference(cnf_transformation,[],[f41])).
% 1.62/0.58  fof(f41,plain,(
% 1.62/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.62/0.58    inference(ennf_transformation,[],[f2])).
% 1.62/0.58  fof(f2,axiom,(
% 1.62/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.62/0.58  fof(f106,plain,(
% 1.62/0.58    r1_tarski(sK2,k2_zfmisc_1(sK0,sK0))),
% 1.62/0.58    inference(resolution,[],[f54,f75])).
% 1.62/0.58  fof(f75,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f50])).
% 1.62/0.58  fof(f50,plain,(
% 1.62/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.62/0.58    inference(nnf_transformation,[],[f3])).
% 1.62/0.58  fof(f3,axiom,(
% 1.62/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.62/0.58  fof(f341,plain,(
% 1.62/0.58    ( ! [X1] : (k7_relat_1(sK2,X1) = k3_xboole_0(sK2,k2_zfmisc_1(X1,sK0))) )),
% 1.62/0.58    inference(backward_demodulation,[],[f118,f338])).
% 1.62/0.58  fof(f338,plain,(
% 1.62/0.58    sK0 = k2_relat_1(sK2)),
% 1.62/0.58    inference(subsumption_resolution,[],[f337,f127])).
% 1.62/0.58  fof(f127,plain,(
% 1.62/0.58    r1_tarski(k2_relat_1(sK2),sK0)),
% 1.62/0.58    inference(resolution,[],[f126,f75])).
% 1.62/0.58  fof(f126,plain,(
% 1.62/0.58    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0))),
% 1.62/0.58    inference(subsumption_resolution,[],[f125,f54])).
% 1.62/0.58  fof(f125,plain,(
% 1.62/0.58    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.62/0.58    inference(superposition,[],[f69,f104])).
% 1.62/0.58  fof(f104,plain,(
% 1.62/0.58    k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2)),
% 1.62/0.58    inference(resolution,[],[f54,f60])).
% 1.62/0.58  fof(f60,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f27])).
% 1.62/0.58  fof(f27,plain,(
% 1.62/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.58    inference(ennf_transformation,[],[f15])).
% 1.62/0.58  fof(f15,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.62/0.58  fof(f69,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f33])).
% 1.62/0.58  fof(f33,plain,(
% 1.62/0.58    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.58    inference(ennf_transformation,[],[f14])).
% 1.62/0.58  fof(f14,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.62/0.58  fof(f337,plain,(
% 1.62/0.58    sK0 = k2_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK0)),
% 1.62/0.58    inference(resolution,[],[f335,f63])).
% 1.62/0.58  fof(f63,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f48])).
% 1.62/0.58  fof(f48,plain,(
% 1.62/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.62/0.58    inference(flattening,[],[f47])).
% 1.62/0.58  fof(f47,plain,(
% 1.62/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.62/0.58    inference(nnf_transformation,[],[f1])).
% 1.62/0.58  fof(f1,axiom,(
% 1.62/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.62/0.58  fof(f335,plain,(
% 1.62/0.58    r1_tarski(sK0,k2_relat_1(sK2))),
% 1.62/0.58    inference(forward_demodulation,[],[f334,f98])).
% 1.62/0.58  fof(f98,plain,(
% 1.62/0.58    sK0 = k2_relat_1(sK1)),
% 1.62/0.58    inference(forward_demodulation,[],[f94,f56])).
% 1.62/0.58  fof(f56,plain,(
% 1.62/0.58    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  fof(f94,plain,(
% 1.62/0.58    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)),
% 1.62/0.58    inference(resolution,[],[f52,f60])).
% 1.62/0.58  fof(f52,plain,(
% 1.62/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  fof(f334,plain,(
% 1.62/0.58    r1_tarski(k2_relat_1(sK1),k2_relat_1(sK2))),
% 1.62/0.58    inference(forward_demodulation,[],[f332,f261])).
% 1.62/0.58  fof(f261,plain,(
% 1.62/0.58    sK1 = k5_relat_1(sK1,sK2)),
% 1.62/0.58    inference(subsumption_resolution,[],[f249,f186])).
% 1.62/0.58  fof(f186,plain,(
% 1.62/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)),
% 1.62/0.58    inference(backward_demodulation,[],[f55,f185])).
% 1.62/0.58  fof(f185,plain,(
% 1.62/0.58    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)),
% 1.62/0.58    inference(subsumption_resolution,[],[f181,f51])).
% 1.62/0.58  fof(f51,plain,(
% 1.62/0.58    v1_funct_1(sK1)),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  fof(f181,plain,(
% 1.62/0.58    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) | ~v1_funct_1(sK1)),
% 1.62/0.58    inference(resolution,[],[f108,f52])).
% 1.62/0.58  fof(f108,plain,(
% 1.62/0.58    ( ! [X6,X4,X5] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k1_partfun1(X4,X5,sK0,sK0,X6,sK2) = k5_relat_1(X6,sK2) | ~v1_funct_1(X6)) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f105,f53])).
% 1.62/0.58  fof(f105,plain,(
% 1.62/0.58    ( ! [X6,X4,X5] : (k1_partfun1(X4,X5,sK0,sK0,X6,sK2) = k5_relat_1(X6,sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X6)) )),
% 1.62/0.58    inference(resolution,[],[f54,f59])).
% 1.62/0.58  fof(f59,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f26])).
% 1.62/0.58  fof(f26,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.62/0.58    inference(flattening,[],[f25])).
% 1.62/0.58  fof(f25,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.62/0.58    inference(ennf_transformation,[],[f18])).
% 1.62/0.58  fof(f18,axiom,(
% 1.62/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.62/0.58  fof(f55,plain,(
% 1.62/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  fof(f249,plain,(
% 1.62/0.58    sK1 = k5_relat_1(sK1,sK2) | ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)),
% 1.62/0.58    inference(resolution,[],[f201,f92])).
% 1.62/0.58  fof(f92,plain,(
% 1.62/0.58    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = X3 | ~r2_relset_1(sK0,sK0,X3,sK1)) )),
% 1.62/0.58    inference(resolution,[],[f52,f70])).
% 1.62/0.58  fof(f70,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f49])).
% 1.62/0.58  fof(f201,plain,(
% 1.62/0.58    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.62/0.58    inference(forward_demodulation,[],[f200,f185])).
% 1.62/0.58  fof(f200,plain,(
% 1.62/0.58    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.62/0.58    inference(subsumption_resolution,[],[f196,f51])).
% 1.62/0.58  fof(f196,plain,(
% 1.62/0.58    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 1.62/0.58    inference(resolution,[],[f107,f52])).
% 1.62/0.58  fof(f107,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_funct_1(X2)) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f101,f53])).
% 1.62/0.58  fof(f101,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (m1_subset_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.62/0.58    inference(resolution,[],[f54,f73])).
% 1.62/0.58  fof(f73,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f37])).
% 1.62/0.58  fof(f37,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.62/0.58    inference(flattening,[],[f36])).
% 1.62/0.58  fof(f36,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.62/0.58    inference(ennf_transformation,[],[f17])).
% 1.62/0.58  fof(f17,axiom,(
% 1.62/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.62/0.58  fof(f332,plain,(
% 1.62/0.58    r1_tarski(k2_relat_1(k5_relat_1(sK1,sK2)),k2_relat_1(sK2))),
% 1.62/0.58    inference(resolution,[],[f117,f90])).
% 1.62/0.58  fof(f90,plain,(
% 1.62/0.58    v1_relat_1(sK1)),
% 1.62/0.58    inference(resolution,[],[f52,f74])).
% 1.62/0.58  fof(f117,plain,(
% 1.62/0.58    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(k5_relat_1(X0,sK2)),k2_relat_1(sK2))) )),
% 1.62/0.58    inference(resolution,[],[f100,f81])).
% 1.62/0.58  fof(f81,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f40])).
% 1.62/0.58  fof(f40,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f5])).
% 1.62/0.58  fof(f5,axiom,(
% 1.62/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.62/0.58  fof(f118,plain,(
% 1.62/0.58    ( ! [X1] : (k7_relat_1(sK2,X1) = k3_xboole_0(sK2,k2_zfmisc_1(X1,k2_relat_1(sK2)))) )),
% 1.62/0.58    inference(resolution,[],[f100,f77])).
% 1.62/0.58  fof(f77,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f39])).
% 1.62/0.58  fof(f39,plain,(
% 1.62/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.62/0.58    inference(ennf_transformation,[],[f9])).
% 1.62/0.58  fof(f9,axiom,(
% 1.62/0.58    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).
% 1.62/0.58  fof(f326,plain,(
% 1.62/0.58    sK0 = k1_relat_1(k7_relat_1(sK2,sK0))),
% 1.62/0.58    inference(subsumption_resolution,[],[f323,f100])).
% 1.62/0.58  fof(f323,plain,(
% 1.62/0.58    sK0 = k1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2)),
% 1.62/0.58    inference(resolution,[],[f291,f83])).
% 1.62/0.58  fof(f83,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f43])).
% 1.62/0.58  fof(f43,plain,(
% 1.62/0.58    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.62/0.58    inference(flattening,[],[f42])).
% 1.62/0.58  fof(f42,plain,(
% 1.62/0.58    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.62/0.58    inference(ennf_transformation,[],[f8])).
% 1.62/0.58  fof(f8,axiom,(
% 1.62/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.62/0.58  fof(f291,plain,(
% 1.62/0.58    r1_tarski(sK0,k1_relat_1(sK2))),
% 1.62/0.58    inference(forward_demodulation,[],[f290,f98])).
% 1.62/0.58  fof(f290,plain,(
% 1.62/0.58    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))),
% 1.62/0.58    inference(subsumption_resolution,[],[f289,f100])).
% 1.62/0.58  fof(f289,plain,(
% 1.62/0.58    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.62/0.58    inference(subsumption_resolution,[],[f288,f53])).
% 1.62/0.58  fof(f288,plain,(
% 1.62/0.58    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.62/0.58    inference(subsumption_resolution,[],[f287,f90])).
% 1.62/0.58  fof(f287,plain,(
% 1.62/0.58    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.62/0.58    inference(subsumption_resolution,[],[f286,f51])).
% 1.62/0.58  fof(f286,plain,(
% 1.62/0.58    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.62/0.58    inference(trivial_inequality_removal,[],[f283])).
% 1.62/0.58  fof(f283,plain,(
% 1.62/0.58    k1_relat_1(sK1) != k1_relat_1(sK1) | r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.62/0.58    inference(superposition,[],[f65,f261])).
% 1.62/0.58  fof(f65,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f31])).
% 1.62/0.58  fof(f31,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.58    inference(flattening,[],[f30])).
% 1.62/0.58  fof(f30,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f12])).
% 1.62/0.58  fof(f12,axiom,(
% 1.62/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 1.62/0.58  fof(f505,plain,(
% 1.62/0.58    sK0 != k1_relat_1(sK2) | sK2 = k6_relat_1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.62/0.58    inference(trivial_inequality_removal,[],[f504])).
% 1.62/0.58  fof(f504,plain,(
% 1.62/0.58    sK1 != sK1 | sK0 != k1_relat_1(sK2) | sK2 = k6_relat_1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.62/0.58    inference(superposition,[],[f154,f261])).
% 1.62/0.58  fof(f154,plain,(
% 1.62/0.58    ( ! [X0] : (sK1 != k5_relat_1(sK1,X0) | k1_relat_1(X0) != sK0 | k6_relat_1(sK0) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f153,f98])).
% 1.62/0.58  fof(f153,plain,(
% 1.62/0.58    ( ! [X0] : (sK0 != k2_relat_1(sK1) | k1_relat_1(X0) != sK0 | sK1 != k5_relat_1(sK1,X0) | k6_relat_1(sK0) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.58    inference(forward_demodulation,[],[f152,f67])).
% 1.62/0.58  fof(f67,plain,(
% 1.62/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.62/0.58    inference(cnf_transformation,[],[f6])).
% 1.62/0.58  fof(f6,axiom,(
% 1.62/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.62/0.58  fof(f152,plain,(
% 1.62/0.58    ( ! [X0] : (k1_relat_1(X0) != sK0 | sK1 != k5_relat_1(sK1,X0) | k6_relat_1(sK0) = X0 | k2_relat_1(sK1) != k1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.58    inference(forward_demodulation,[],[f151,f67])).
% 1.62/0.58  fof(f151,plain,(
% 1.62/0.58    ( ! [X0] : (sK1 != k5_relat_1(sK1,X0) | k6_relat_1(sK0) = X0 | k1_relat_1(X0) != k1_relat_1(k6_relat_1(sK0)) | k2_relat_1(sK1) != k1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f150,f90])).
% 1.62/0.58  fof(f150,plain,(
% 1.62/0.58    ( ! [X0] : (sK1 != k5_relat_1(sK1,X0) | k6_relat_1(sK0) = X0 | k1_relat_1(X0) != k1_relat_1(k6_relat_1(sK0)) | k2_relat_1(sK1) != k1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK1)) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f149,f51])).
% 1.62/0.58  fof(f149,plain,(
% 1.62/0.58    ( ! [X0] : (sK1 != k5_relat_1(sK1,X0) | k6_relat_1(sK0) = X0 | k1_relat_1(X0) != k1_relat_1(k6_relat_1(sK0)) | k2_relat_1(sK1) != k1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f148,f80])).
% 1.62/0.58  fof(f80,plain,(
% 1.62/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f4])).
% 1.62/0.58  fof(f4,axiom,(
% 1.62/0.58    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.62/0.58  fof(f148,plain,(
% 1.62/0.58    ( ! [X0] : (sK1 != k5_relat_1(sK1,X0) | k6_relat_1(sK0) = X0 | k1_relat_1(X0) != k1_relat_1(k6_relat_1(sK0)) | k2_relat_1(sK1) != k1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f139,f79])).
% 1.62/0.58  fof(f79,plain,(
% 1.62/0.58    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f10])).
% 1.62/0.58  fof(f10,axiom,(
% 1.62/0.58    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.62/0.58  fof(f139,plain,(
% 1.62/0.58    ( ! [X0] : (sK1 != k5_relat_1(sK1,X0) | k6_relat_1(sK0) = X0 | k1_relat_1(X0) != k1_relat_1(k6_relat_1(sK0)) | k2_relat_1(sK1) != k1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.62/0.58    inference(superposition,[],[f86,f114])).
% 1.62/0.58  fof(f114,plain,(
% 1.62/0.58    sK1 = k5_relat_1(sK1,k6_relat_1(sK0))),
% 1.62/0.58    inference(forward_demodulation,[],[f111,f98])).
% 1.62/0.58  fof(f111,plain,(
% 1.62/0.58    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 1.62/0.58    inference(resolution,[],[f90,f66])).
% 1.62/0.58  fof(f66,plain,(
% 1.62/0.58    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.62/0.58    inference(cnf_transformation,[],[f32])).
% 1.62/0.58  fof(f32,plain,(
% 1.62/0.58    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f7])).
% 1.62/0.58  fof(f7,axiom,(
% 1.62/0.58    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.62/0.58  fof(f86,plain,(
% 1.62/0.58    ( ! [X2,X3,X1] : (k5_relat_1(X1,X2) != k5_relat_1(X1,X3) | X2 = X3 | k1_relat_1(X2) != k1_relat_1(X3) | k2_relat_1(X1) != k1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.62/0.58    inference(equality_resolution,[],[f64])).
% 1.62/0.58  fof(f64,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (X2 = X3 | k5_relat_1(X1,X2) != k5_relat_1(X1,X3) | k1_relat_1(X3) != X0 | k1_relat_1(X2) != X0 | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f29])).
% 1.62/0.58  fof(f29,plain,(
% 1.62/0.58    ! [X0,X1] : (! [X2] : (! [X3] : (X2 = X3 | k5_relat_1(X1,X2) != k5_relat_1(X1,X3) | k1_relat_1(X3) != X0 | k1_relat_1(X2) != X0 | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.62/0.58    inference(flattening,[],[f28])).
% 1.62/0.58  fof(f28,plain,(
% 1.62/0.58    ! [X0,X1] : (! [X2] : (! [X3] : ((X2 = X3 | (k5_relat_1(X1,X2) != k5_relat_1(X1,X3) | k1_relat_1(X3) != X0 | k1_relat_1(X2) != X0 | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.62/0.58    inference(ennf_transformation,[],[f11])).
% 1.62/0.58  fof(f11,axiom,(
% 1.62/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_1)).
% 1.62/0.58  fof(f89,plain,(
% 1.62/0.58    ~r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))),
% 1.62/0.58    inference(forward_demodulation,[],[f57,f58])).
% 1.62/0.58  fof(f58,plain,(
% 1.62/0.58    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f19])).
% 1.62/0.58  fof(f19,axiom,(
% 1.62/0.58    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.62/0.58  fof(f57,plain,(
% 1.62/0.58    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  % SZS output end Proof for theBenchmark
% 1.62/0.58  % (14701)------------------------------
% 1.62/0.58  % (14701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (14701)Termination reason: Refutation
% 1.62/0.58  
% 1.62/0.58  % (14701)Memory used [KB]: 2046
% 1.62/0.58  % (14701)Time elapsed: 0.174 s
% 1.62/0.58  % (14701)------------------------------
% 1.62/0.58  % (14701)------------------------------
% 1.62/0.59  % (14686)Success in time 0.224 s
%------------------------------------------------------------------------------
