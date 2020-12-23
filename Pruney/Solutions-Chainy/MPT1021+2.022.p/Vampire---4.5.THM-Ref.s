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
% DateTime   : Thu Dec  3 13:05:53 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  158 (3380 expanded)
%              Number of leaves         :   18 ( 809 expanded)
%              Depth                    :   27
%              Number of atoms          :  472 (17496 expanded)
%              Number of equality atoms :  127 ( 922 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f719,plain,(
    $false ),
    inference(subsumption_resolution,[],[f718,f317])).

fof(f317,plain,(
    ! [X0] : r2_relset_1(k1_xboole_0,X0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f244,f312])).

fof(f312,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f235,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f235,plain,(
    r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f110,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f110,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f103,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f75])).

% (21028)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f103,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f61,f60])).

fof(f60,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f244,plain,(
    ! [X0] : r2_relset_1(k1_xboole_0,X0,k6_relat_1(k1_xboole_0),k6_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f126,f110])).

fof(f126,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | r2_relset_1(k1_xboole_0,X2,X3,X3) ) ),
    inference(superposition,[],[f100,f93])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f718,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f707,f312])).

fof(f707,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f688,f698])).

fof(f698,plain,(
    k1_xboole_0 = k1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f555,f697])).

fof(f697,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f689,f637])).

fof(f637,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f551,f92])).

fof(f551,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f56,f548])).

fof(f548,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f547,f124])).

fof(f124,plain,(
    ! [X0] : r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(resolution,[],[f100,f103])).

fof(f547,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f546,f223])).

fof(f223,plain,
    ( sK0 = k1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f144,f127])).

fof(f127,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f77,f56])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f144,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f143,f56])).

fof(f143,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f79,f54])).

fof(f54,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f46])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f546,plain,(
    ~ r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f437,f543])).

fof(f543,plain,(
    k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    inference(resolution,[],[f454,f175])).

fof(f175,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f174,f157])).

fof(f157,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f156,f53])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f156,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f155,f55])).

fof(f55,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f155,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f154,f56])).

fof(f154,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f67,f54])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f174,plain,(
    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f173,f53])).

fof(f173,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f172,f55])).

fof(f172,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f171,f56])).

fof(f171,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f71,f54])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f454,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,X0,X1,sK1,k2_funct_1(sK1)) ) ),
    inference(resolution,[],[f310,f56])).

fof(f310,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(X0,X1,X2,X3,sK1,k2_funct_1(sK1))
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(forward_demodulation,[],[f307,f139])).

fof(f139,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f138,f112])).

fof(f112,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f76,f56])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f138,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f135,f53])).

fof(f135,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f133,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f133,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f132,f56])).

fof(f132,plain,
    ( v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f131,f53])).

fof(f131,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f86,f55])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f307,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(X0,X1,X2,X3,sK1,k2_funct_1(sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f181,f53])).

fof(f181,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | k1_partfun1(X2,X3,X0,X1,X4,k2_funct_1(sK1)) = k5_relat_1(X4,k2_funct_1(sK1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f158,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f158,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f153,f157])).

fof(f153,plain,(
    v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f152,f53])).

fof(f152,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f151,f55])).

fof(f151,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f150,f56])).

fof(f150,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f68,f54])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | v1_funct_1(k2_funct_2(X0,X1))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f437,plain,(
    ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f436,f124])).

fof(f436,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f160,f433])).

fof(f433,plain,(
    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(resolution,[],[f304,f56])).

fof(f304,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1) ) ),
    inference(resolution,[],[f227,f175])).

fof(f227,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k6_relat_1(sK0) = k1_partfun1(X4,X5,X6,X7,k2_funct_1(sK1),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(forward_demodulation,[],[f226,f180])).

fof(f180,plain,(
    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(backward_demodulation,[],[f137,f179])).

fof(f179,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f178,f112])).

fof(f178,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f177,f116])).

fof(f116,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f78,f56])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f177,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f142,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f142,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f141,f56])).

fof(f141,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f140,f53])).

fof(f140,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f87,f55])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f137,plain,(
    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f136,f112])).

fof(f136,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f134,f53])).

fof(f134,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f133,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f226,plain,(
    ! [X6,X4,X7,X5] :
      ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(X4,X5,X6,X7,k2_funct_1(sK1),sK1)
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f176,f158])).

fof(f176,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | k1_partfun1(X2,X3,X0,X1,X4,sK1) = k5_relat_1(X4,sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f90,f53])).

fof(f160,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f159,f157])).

fof(f159,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f102,f157])).

fof(f102,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f101,f60])).

fof(f101,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f57,f60])).

fof(f57,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f689,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f549,f107])).

fof(f107,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f98,f93])).

fof(f98,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f549,plain,(
    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f54,f548])).

fof(f555,plain,(
    k1_relat_1(sK1) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f127,f548])).

fof(f688,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f636,f312])).

fof(f636,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f546,f548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 12:54:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.49  % (21040)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.18/0.49  % (21032)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.18/0.49  % (21022)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.49  % (21023)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.18/0.49  % (21021)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.50  % (21020)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.18/0.50  % (21030)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.18/0.50  % (21039)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.18/0.51  % (21038)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.18/0.51  % (21019)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.18/0.51  % (21017)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.18/0.51  % (21036)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.18/0.51  % (21024)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.18/0.51  % (21018)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.18/0.51  % (21016)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.18/0.51  % (21031)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.18/0.51  % (21045)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.18/0.52  % (21035)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.18/0.52  % (21033)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.18/0.52  % (21046)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.18/0.52  % (21033)Refutation not found, incomplete strategy% (21033)------------------------------
% 0.18/0.52  % (21033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.52  % (21033)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.52  
% 0.18/0.52  % (21033)Memory used [KB]: 10746
% 0.18/0.52  % (21033)Time elapsed: 0.129 s
% 0.18/0.52  % (21033)------------------------------
% 0.18/0.52  % (21033)------------------------------
% 0.18/0.52  % (21034)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.18/0.52  % (21044)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.18/0.52  % (21042)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.18/0.52  % (21041)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.18/0.53  % (21037)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.18/0.53  % (21043)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.18/0.53  % (21026)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.18/0.53  % (21025)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.18/0.53  % (21029)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.18/0.53  % (21023)Refutation found. Thanks to Tanya!
% 0.18/0.53  % SZS status Theorem for theBenchmark
% 0.18/0.53  % SZS output start Proof for theBenchmark
% 0.18/0.53  fof(f719,plain,(
% 0.18/0.53    $false),
% 0.18/0.53    inference(subsumption_resolution,[],[f718,f317])).
% 0.18/0.53  fof(f317,plain,(
% 0.18/0.53    ( ! [X0] : (r2_relset_1(k1_xboole_0,X0,k1_xboole_0,k1_xboole_0)) )),
% 0.18/0.53    inference(backward_demodulation,[],[f244,f312])).
% 0.18/0.53  fof(f312,plain,(
% 0.18/0.53    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.18/0.53    inference(resolution,[],[f235,f62])).
% 0.18/0.53  fof(f62,plain,(
% 0.18/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.18/0.53    inference(cnf_transformation,[],[f25])).
% 0.18/0.53  fof(f25,plain,(
% 0.18/0.53    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.18/0.53    inference(ennf_transformation,[],[f1])).
% 0.18/0.53  fof(f1,axiom,(
% 0.18/0.53    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.18/0.53  fof(f235,plain,(
% 0.18/0.53    r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.18/0.53    inference(resolution,[],[f110,f72])).
% 0.18/0.53  fof(f72,plain,(
% 0.18/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f34])).
% 0.18/0.53  fof(f34,plain,(
% 0.18/0.53    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.18/0.53    inference(ennf_transformation,[],[f20])).
% 0.18/0.53  fof(f20,plain,(
% 0.18/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.18/0.53    inference(unused_predicate_definition_removal,[],[f3])).
% 0.18/0.53  fof(f3,axiom,(
% 0.18/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.18/0.53  fof(f110,plain,(
% 0.18/0.53    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.18/0.53    inference(superposition,[],[f103,f92])).
% 0.18/0.53  fof(f92,plain,(
% 0.18/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.18/0.53    inference(equality_resolution,[],[f75])).
% 0.18/0.53  % (21028)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.18/0.53  fof(f75,plain,(
% 0.18/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.18/0.53    inference(cnf_transformation,[],[f50])).
% 0.18/0.53  fof(f50,plain,(
% 0.18/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.18/0.53    inference(flattening,[],[f49])).
% 0.18/0.53  fof(f49,plain,(
% 0.18/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.18/0.53    inference(nnf_transformation,[],[f2])).
% 0.18/0.53  fof(f2,axiom,(
% 0.18/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.18/0.53  fof(f103,plain,(
% 0.18/0.53    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.18/0.53    inference(forward_demodulation,[],[f61,f60])).
% 0.18/0.53  fof(f60,plain,(
% 0.18/0.53    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f17])).
% 0.18/0.53  fof(f17,axiom,(
% 0.18/0.53    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.18/0.53  fof(f61,plain,(
% 0.18/0.53    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.18/0.53    inference(cnf_transformation,[],[f21])).
% 0.18/0.53  fof(f21,plain,(
% 0.18/0.53    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.18/0.53    inference(pure_predicate_removal,[],[f14])).
% 0.18/0.53  fof(f14,axiom,(
% 0.18/0.53    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.18/0.53  fof(f244,plain,(
% 0.18/0.53    ( ! [X0] : (r2_relset_1(k1_xboole_0,X0,k6_relat_1(k1_xboole_0),k6_relat_1(k1_xboole_0))) )),
% 0.18/0.53    inference(resolution,[],[f126,f110])).
% 0.18/0.53  fof(f126,plain,(
% 0.18/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | r2_relset_1(k1_xboole_0,X2,X3,X3)) )),
% 0.18/0.53    inference(superposition,[],[f100,f93])).
% 0.18/0.53  fof(f93,plain,(
% 0.18/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.18/0.53    inference(equality_resolution,[],[f74])).
% 0.18/0.54  fof(f74,plain,(
% 0.18/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.18/0.54    inference(cnf_transformation,[],[f50])).
% 0.18/0.54  fof(f100,plain,(
% 0.18/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.18/0.54    inference(duplicate_literal_removal,[],[f99])).
% 0.18/0.54  fof(f99,plain,(
% 0.18/0.54    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.54    inference(equality_resolution,[],[f89])).
% 0.18/0.54  fof(f89,plain,(
% 0.18/0.54    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.54    inference(cnf_transformation,[],[f52])).
% 0.18/0.54  fof(f52,plain,(
% 0.18/0.54    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.54    inference(nnf_transformation,[],[f43])).
% 0.18/0.54  fof(f43,plain,(
% 0.18/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.54    inference(flattening,[],[f42])).
% 0.18/0.54  fof(f42,plain,(
% 0.18/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.18/0.54    inference(ennf_transformation,[],[f9])).
% 0.18/0.54  fof(f9,axiom,(
% 0.18/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.18/0.54  fof(f718,plain,(
% 0.18/0.54    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.18/0.54    inference(forward_demodulation,[],[f707,f312])).
% 0.18/0.54  fof(f707,plain,(
% 0.18/0.54    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.18/0.54    inference(backward_demodulation,[],[f688,f698])).
% 0.18/0.54  fof(f698,plain,(
% 0.18/0.54    k1_xboole_0 = k1_relat_1(sK1)),
% 0.18/0.54    inference(backward_demodulation,[],[f555,f697])).
% 0.18/0.54  fof(f697,plain,(
% 0.18/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.18/0.54    inference(subsumption_resolution,[],[f689,f637])).
% 0.18/0.54  fof(f637,plain,(
% 0.18/0.54    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 0.18/0.54    inference(forward_demodulation,[],[f551,f92])).
% 0.18/0.54  fof(f551,plain,(
% 0.18/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.18/0.54    inference(backward_demodulation,[],[f56,f548])).
% 0.18/0.54  fof(f548,plain,(
% 0.18/0.54    k1_xboole_0 = sK0),
% 0.18/0.54    inference(subsumption_resolution,[],[f547,f124])).
% 0.18/0.54  fof(f124,plain,(
% 0.18/0.54    ( ! [X0] : (r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0))) )),
% 0.18/0.54    inference(resolution,[],[f100,f103])).
% 0.18/0.54  fof(f547,plain,(
% 0.18/0.54    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | k1_xboole_0 = sK0),
% 0.18/0.54    inference(superposition,[],[f546,f223])).
% 0.18/0.54  fof(f223,plain,(
% 0.18/0.54    sK0 = k1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.18/0.54    inference(superposition,[],[f144,f127])).
% 0.18/0.54  fof(f127,plain,(
% 0.18/0.54    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 0.18/0.54    inference(resolution,[],[f77,f56])).
% 0.18/0.54  fof(f77,plain,(
% 0.18/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f36])).
% 0.18/0.54  fof(f36,plain,(
% 0.18/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.54    inference(ennf_transformation,[],[f8])).
% 0.18/0.54  fof(f8,axiom,(
% 0.18/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.18/0.54  fof(f144,plain,(
% 0.18/0.54    sK0 = k1_relset_1(sK0,sK0,sK1) | k1_xboole_0 = sK0),
% 0.18/0.54    inference(subsumption_resolution,[],[f143,f56])).
% 0.18/0.54  fof(f143,plain,(
% 0.18/0.54    sK0 = k1_relset_1(sK0,sK0,sK1) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.54    inference(resolution,[],[f79,f54])).
% 0.18/0.54  fof(f54,plain,(
% 0.18/0.54    v1_funct_2(sK1,sK0,sK0)),
% 0.18/0.54    inference(cnf_transformation,[],[f47])).
% 0.18/0.54  fof(f47,plain,(
% 0.18/0.54    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.18/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f46])).
% 0.18/0.54  fof(f46,plain,(
% 0.18/0.54    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.18/0.54    introduced(choice_axiom,[])).
% 0.18/0.54  fof(f24,plain,(
% 0.18/0.54    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.18/0.54    inference(flattening,[],[f23])).
% 0.18/0.54  fof(f23,plain,(
% 0.18/0.54    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.18/0.54    inference(ennf_transformation,[],[f19])).
% 0.18/0.54  fof(f19,negated_conjecture,(
% 0.18/0.54    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.18/0.54    inference(negated_conjecture,[],[f18])).
% 0.18/0.54  fof(f18,conjecture,(
% 0.18/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 0.18/0.54  fof(f79,plain,(
% 0.18/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.54    inference(cnf_transformation,[],[f51])).
% 0.18/0.54  fof(f51,plain,(
% 0.18/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.54    inference(nnf_transformation,[],[f39])).
% 0.18/0.54  fof(f39,plain,(
% 0.18/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.54    inference(flattening,[],[f38])).
% 0.18/0.54  fof(f38,plain,(
% 0.18/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.54    inference(ennf_transformation,[],[f11])).
% 0.18/0.54  fof(f11,axiom,(
% 0.18/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.18/0.54  fof(f546,plain,(
% 0.18/0.54    ~r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0))),
% 0.18/0.54    inference(backward_demodulation,[],[f437,f543])).
% 0.18/0.54  fof(f543,plain,(
% 0.18/0.54    k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 0.18/0.54    inference(resolution,[],[f454,f175])).
% 0.18/0.54  fof(f175,plain,(
% 0.18/0.54    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.54    inference(forward_demodulation,[],[f174,f157])).
% 0.18/0.54  fof(f157,plain,(
% 0.18/0.54    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.18/0.54    inference(subsumption_resolution,[],[f156,f53])).
% 0.18/0.54  fof(f53,plain,(
% 0.18/0.54    v1_funct_1(sK1)),
% 0.18/0.54    inference(cnf_transformation,[],[f47])).
% 0.18/0.54  fof(f156,plain,(
% 0.18/0.54    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.18/0.54    inference(subsumption_resolution,[],[f155,f55])).
% 0.18/0.54  fof(f55,plain,(
% 0.18/0.54    v3_funct_2(sK1,sK0,sK0)),
% 0.18/0.54    inference(cnf_transformation,[],[f47])).
% 0.18/0.54  fof(f155,plain,(
% 0.18/0.54    ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.18/0.54    inference(subsumption_resolution,[],[f154,f56])).
% 0.18/0.54  fof(f154,plain,(
% 0.18/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.18/0.54    inference(resolution,[],[f67,f54])).
% 0.18/0.54  fof(f67,plain,(
% 0.18/0.54    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f31])).
% 0.18/0.54  fof(f31,plain,(
% 0.18/0.54    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.18/0.54    inference(flattening,[],[f30])).
% 0.18/0.54  fof(f30,plain,(
% 0.18/0.54    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.18/0.54    inference(ennf_transformation,[],[f16])).
% 0.18/0.54  fof(f16,axiom,(
% 0.18/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.18/0.54  fof(f174,plain,(
% 0.18/0.54    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.54    inference(subsumption_resolution,[],[f173,f53])).
% 0.18/0.54  fof(f173,plain,(
% 0.18/0.54    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 0.18/0.54    inference(subsumption_resolution,[],[f172,f55])).
% 0.18/0.54  fof(f172,plain,(
% 0.18/0.54    ~v3_funct_2(sK1,sK0,sK0) | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 0.18/0.54    inference(subsumption_resolution,[],[f171,f56])).
% 0.18/0.54  fof(f171,plain,(
% 0.18/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 0.18/0.54    inference(resolution,[],[f71,f54])).
% 0.18/0.54  fof(f71,plain,(
% 0.18/0.54    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X1)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f33])).
% 0.18/0.54  fof(f33,plain,(
% 0.18/0.54    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.18/0.54    inference(flattening,[],[f32])).
% 0.18/0.54  fof(f32,plain,(
% 0.18/0.54    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.18/0.54    inference(ennf_transformation,[],[f13])).
% 0.18/0.54  fof(f13,axiom,(
% 0.18/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.18/0.54  fof(f454,plain,(
% 0.18/0.54    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,X0,X1,sK1,k2_funct_1(sK1))) )),
% 0.18/0.54    inference(resolution,[],[f310,f56])).
% 0.18/0.54  fof(f310,plain,(
% 0.18/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(X0,X1,X2,X3,sK1,k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.18/0.54    inference(forward_demodulation,[],[f307,f139])).
% 0.18/0.54  fof(f139,plain,(
% 0.18/0.54    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 0.18/0.54    inference(subsumption_resolution,[],[f138,f112])).
% 0.18/0.54  fof(f112,plain,(
% 0.18/0.54    v1_relat_1(sK1)),
% 0.18/0.54    inference(resolution,[],[f76,f56])).
% 0.18/0.54  fof(f76,plain,(
% 0.18/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f35])).
% 0.18/0.54  fof(f35,plain,(
% 0.18/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.54    inference(ennf_transformation,[],[f6])).
% 0.18/0.54  fof(f6,axiom,(
% 0.18/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.18/0.54  fof(f138,plain,(
% 0.18/0.54    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.18/0.54    inference(subsumption_resolution,[],[f135,f53])).
% 0.18/0.54  fof(f135,plain,(
% 0.18/0.54    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.18/0.54    inference(resolution,[],[f133,f63])).
% 0.18/0.54  fof(f63,plain,(
% 0.18/0.54    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f27])).
% 0.18/0.54  fof(f27,plain,(
% 0.18/0.54    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.54    inference(flattening,[],[f26])).
% 0.18/0.54  fof(f26,plain,(
% 0.18/0.54    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.54    inference(ennf_transformation,[],[f5])).
% 0.18/0.54  fof(f5,axiom,(
% 0.18/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.18/0.54  fof(f133,plain,(
% 0.18/0.54    v2_funct_1(sK1)),
% 0.18/0.54    inference(subsumption_resolution,[],[f132,f56])).
% 0.18/0.54  fof(f132,plain,(
% 0.18/0.54    v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.54    inference(subsumption_resolution,[],[f131,f53])).
% 0.18/0.54  fof(f131,plain,(
% 0.18/0.54    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.54    inference(resolution,[],[f86,f55])).
% 0.18/0.54  fof(f86,plain,(
% 0.18/0.54    ( ! [X2,X0,X1] : (~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.54    inference(cnf_transformation,[],[f41])).
% 0.18/0.54  fof(f41,plain,(
% 0.18/0.54    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.54    inference(flattening,[],[f40])).
% 0.18/0.54  fof(f40,plain,(
% 0.18/0.54    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.54    inference(ennf_transformation,[],[f10])).
% 0.18/0.54  fof(f10,axiom,(
% 0.18/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.18/0.54  fof(f307,plain,(
% 0.18/0.54    ( ! [X2,X0,X3,X1] : (k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(X0,X1,X2,X3,sK1,k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.18/0.54    inference(resolution,[],[f181,f53])).
% 0.18/0.54  fof(f181,plain,(
% 0.18/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | k1_partfun1(X2,X3,X0,X1,X4,k2_funct_1(sK1)) = k5_relat_1(X4,k2_funct_1(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.54    inference(resolution,[],[f158,f90])).
% 0.18/0.54  fof(f90,plain,(
% 0.18/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f45])).
% 0.18/0.54  fof(f45,plain,(
% 0.18/0.54    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.18/0.54    inference(flattening,[],[f44])).
% 0.18/0.54  fof(f44,plain,(
% 0.18/0.54    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.18/0.54    inference(ennf_transformation,[],[f15])).
% 0.18/0.54  fof(f15,axiom,(
% 0.18/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.18/0.54  fof(f158,plain,(
% 0.18/0.54    v1_funct_1(k2_funct_1(sK1))),
% 0.18/0.54    inference(backward_demodulation,[],[f153,f157])).
% 0.18/0.54  fof(f153,plain,(
% 0.18/0.54    v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.18/0.54    inference(subsumption_resolution,[],[f152,f53])).
% 0.18/0.54  fof(f152,plain,(
% 0.18/0.54    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1)),
% 0.18/0.54    inference(subsumption_resolution,[],[f151,f55])).
% 0.18/0.54  fof(f151,plain,(
% 0.18/0.54    ~v3_funct_2(sK1,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1)),
% 0.18/0.54    inference(subsumption_resolution,[],[f150,f56])).
% 0.18/0.54  fof(f150,plain,(
% 0.18/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1)),
% 0.18/0.54    inference(resolution,[],[f68,f54])).
% 0.18/0.54  fof(f68,plain,(
% 0.18/0.54    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | v1_funct_1(k2_funct_2(X0,X1)) | ~v1_funct_1(X1)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f33])).
% 0.18/0.54  fof(f437,plain,(
% 0.18/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.18/0.54    inference(subsumption_resolution,[],[f436,f124])).
% 0.18/0.54  fof(f436,plain,(
% 0.18/0.54    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.18/0.54    inference(backward_demodulation,[],[f160,f433])).
% 0.18/0.54  fof(f433,plain,(
% 0.18/0.54    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 0.18/0.54    inference(resolution,[],[f304,f56])).
% 0.18/0.54  fof(f304,plain,(
% 0.18/0.54    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1)) )),
% 0.18/0.54    inference(resolution,[],[f227,f175])).
% 0.18/0.54  fof(f227,plain,(
% 0.18/0.54    ( ! [X6,X4,X7,X5] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k6_relat_1(sK0) = k1_partfun1(X4,X5,X6,X7,k2_funct_1(sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 0.18/0.54    inference(forward_demodulation,[],[f226,f180])).
% 0.18/0.54  fof(f180,plain,(
% 0.18/0.54    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 0.18/0.54    inference(backward_demodulation,[],[f137,f179])).
% 0.18/0.54  fof(f179,plain,(
% 0.18/0.54    sK0 = k2_relat_1(sK1)),
% 0.18/0.54    inference(subsumption_resolution,[],[f178,f112])).
% 0.18/0.54  fof(f178,plain,(
% 0.18/0.54    sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 0.18/0.54    inference(subsumption_resolution,[],[f177,f116])).
% 0.18/0.54  fof(f116,plain,(
% 0.18/0.54    v5_relat_1(sK1,sK0)),
% 0.18/0.54    inference(resolution,[],[f78,f56])).
% 0.18/0.54  fof(f78,plain,(
% 0.18/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f37])).
% 0.18/0.54  fof(f37,plain,(
% 0.18/0.54    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.54    inference(ennf_transformation,[],[f22])).
% 0.18/0.54  fof(f22,plain,(
% 0.18/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.18/0.54    inference(pure_predicate_removal,[],[f7])).
% 0.18/0.54  fof(f7,axiom,(
% 0.18/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.18/0.54  fof(f177,plain,(
% 0.18/0.54    sK0 = k2_relat_1(sK1) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 0.18/0.54    inference(resolution,[],[f142,f65])).
% 0.18/0.54  fof(f65,plain,(
% 0.18/0.54    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f48])).
% 0.18/0.54  fof(f48,plain,(
% 0.18/0.54    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.18/0.54    inference(nnf_transformation,[],[f29])).
% 0.18/0.54  fof(f29,plain,(
% 0.18/0.54    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.18/0.54    inference(flattening,[],[f28])).
% 0.18/0.54  fof(f28,plain,(
% 0.18/0.54    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.18/0.54    inference(ennf_transformation,[],[f12])).
% 0.18/0.54  fof(f12,axiom,(
% 0.18/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.18/0.54  fof(f142,plain,(
% 0.18/0.54    v2_funct_2(sK1,sK0)),
% 0.18/0.54    inference(subsumption_resolution,[],[f141,f56])).
% 0.18/0.54  fof(f141,plain,(
% 0.18/0.54    v2_funct_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.54    inference(subsumption_resolution,[],[f140,f53])).
% 0.18/0.54  fof(f140,plain,(
% 0.18/0.54    v2_funct_2(sK1,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.54    inference(resolution,[],[f87,f55])).
% 0.18/0.54  fof(f87,plain,(
% 0.18/0.54    ( ! [X2,X0,X1] : (~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.54    inference(cnf_transformation,[],[f41])).
% 0.18/0.54  fof(f137,plain,(
% 0.18/0.54    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))),
% 0.18/0.54    inference(subsumption_resolution,[],[f136,f112])).
% 0.18/0.54  fof(f136,plain,(
% 0.18/0.54    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.18/0.54    inference(subsumption_resolution,[],[f134,f53])).
% 0.18/0.54  fof(f134,plain,(
% 0.18/0.54    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.18/0.54    inference(resolution,[],[f133,f64])).
% 0.18/0.54  fof(f64,plain,(
% 0.18/0.54    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f27])).
% 0.18/0.54  fof(f226,plain,(
% 0.18/0.54    ( ! [X6,X4,X7,X5] : (k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(X4,X5,X6,X7,k2_funct_1(sK1),sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 0.18/0.54    inference(resolution,[],[f176,f158])).
% 0.18/0.54  fof(f176,plain,(
% 0.18/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | k1_partfun1(X2,X3,X0,X1,X4,sK1) = k5_relat_1(X4,sK1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.54    inference(resolution,[],[f90,f53])).
% 0.18/0.54  fof(f160,plain,(
% 0.18/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.18/0.54    inference(forward_demodulation,[],[f159,f157])).
% 0.18/0.54  fof(f159,plain,(
% 0.18/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.18/0.54    inference(backward_demodulation,[],[f102,f157])).
% 0.18/0.54  fof(f102,plain,(
% 0.18/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.18/0.54    inference(forward_demodulation,[],[f101,f60])).
% 0.18/0.54  fof(f101,plain,(
% 0.18/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.18/0.54    inference(forward_demodulation,[],[f57,f60])).
% 0.18/0.54  fof(f57,plain,(
% 0.18/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.18/0.54    inference(cnf_transformation,[],[f47])).
% 0.18/0.54  fof(f56,plain,(
% 0.18/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.54    inference(cnf_transformation,[],[f47])).
% 0.18/0.54  fof(f689,plain,(
% 0.18/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 0.18/0.54    inference(resolution,[],[f549,f107])).
% 0.18/0.54  fof(f107,plain,(
% 0.18/0.54    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.18/0.54    inference(forward_demodulation,[],[f98,f93])).
% 0.18/0.54  fof(f98,plain,(
% 0.18/0.54    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.18/0.54    inference(equality_resolution,[],[f80])).
% 0.18/0.54  fof(f80,plain,(
% 0.18/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.54    inference(cnf_transformation,[],[f51])).
% 0.18/0.54  fof(f549,plain,(
% 0.18/0.54    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.18/0.54    inference(backward_demodulation,[],[f54,f548])).
% 0.18/0.54  fof(f555,plain,(
% 0.18/0.54    k1_relat_1(sK1) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.18/0.54    inference(backward_demodulation,[],[f127,f548])).
% 0.18/0.54  fof(f688,plain,(
% 0.18/0.54    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK1)),k1_xboole_0)),
% 0.18/0.54    inference(forward_demodulation,[],[f636,f312])).
% 0.18/0.54  fof(f636,plain,(
% 0.18/0.54    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_xboole_0))),
% 0.18/0.54    inference(backward_demodulation,[],[f546,f548])).
% 0.18/0.54  % SZS output end Proof for theBenchmark
% 0.18/0.54  % (21023)------------------------------
% 0.18/0.54  % (21023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.54  % (21023)Termination reason: Refutation
% 0.18/0.54  
% 0.18/0.54  % (21023)Memory used [KB]: 2174
% 0.18/0.54  % (21023)Time elapsed: 0.101 s
% 0.18/0.54  % (21023)------------------------------
% 0.18/0.54  % (21023)------------------------------
% 0.18/0.54  % (21015)Success in time 0.197 s
%------------------------------------------------------------------------------
