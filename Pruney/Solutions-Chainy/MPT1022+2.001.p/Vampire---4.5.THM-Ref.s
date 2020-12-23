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
% DateTime   : Thu Dec  3 13:06:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  158 (1159 expanded)
%              Number of leaves         :   20 ( 281 expanded)
%              Depth                    :   21
%              Number of atoms          :  452 (6733 expanded)
%              Number of equality atoms :  108 (1724 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f973,plain,(
    $false ),
    inference(subsumption_resolution,[],[f946,f58])).

fof(f58,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
      | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f49])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
        | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) )
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

fof(f946,plain,(
    ~ r1_tarski(sK1,sK0) ),
    inference(backward_demodulation,[],[f552,f930])).

fof(f930,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f929,f392])).

fof(f392,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f391,f301])).

fof(f301,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f121,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f121,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(backward_demodulation,[],[f117,f120])).

fof(f120,plain,(
    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) ),
    inference(subsumption_resolution,[],[f119,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f119,plain,
    ( k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f118,f56])).

fof(f56,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f118,plain,
    ( k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f105,f57])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,
    ( k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f55,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f117,plain,(
    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f116,f54])).

fof(f116,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f115,f56])).

fof(f115,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f104,f57])).

fof(f104,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f55,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f391,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f390,f303])).

fof(f303,plain,(
    v5_relat_1(k2_funct_1(sK2),sK0) ),
    inference(resolution,[],[f121,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f390,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v5_relat_1(k2_funct_1(sK2),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f265,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f265,plain,(
    v2_funct_2(k2_funct_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f264,f121])).

fof(f264,plain,
    ( v2_funct_2(k2_funct_1(sK2),sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f242,f124])).

fof(f124,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f108,f120])).

fof(f108,plain,(
    v1_funct_1(k2_funct_2(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f107,f54])).

fof(f107,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f106,f56])).

fof(f106,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK2))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f101,f57])).

fof(f101,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f55,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f242,plain,
    ( v2_funct_2(k2_funct_1(sK2),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f122,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f122,plain,(
    v3_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    inference(backward_demodulation,[],[f114,f120])).

fof(f114,plain,(
    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f113,f54])).

fof(f113,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f112,f56])).

fof(f112,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f103,f57])).

fof(f103,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f55,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f929,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f927,f850])).

fof(f850,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),sK0) ),
    inference(forward_demodulation,[],[f849,f808])).

fof(f808,plain,(
    sK0 = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f807,f221])).

fof(f221,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f193,f217])).

fof(f217,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f216,f157])).

fof(f157,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f57,f81])).

fof(f216,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f215,f159])).

fof(f159,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f57,f83])).

fof(f215,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f151,f77])).

fof(f151,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f150,f57])).

fof(f150,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f131,f54])).

fof(f131,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f56,f86])).

fof(f193,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(resolution,[],[f157,f62])).

fof(f62,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f807,plain,(
    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f803,f60])).

fof(f60,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f803,plain,(
    k2_subset_1(sK0) = k9_relat_1(sK2,k10_relat_1(sK2,k2_subset_1(sK0))) ),
    inference(resolution,[],[f546,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f546,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | k9_relat_1(sK2,k10_relat_1(sK2,X1)) = X1 ) ),
    inference(resolution,[],[f220,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f220,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,sK0)
      | k9_relat_1(sK2,k10_relat_1(sK2,X6)) = X6 ) ),
    inference(backward_demodulation,[],[f204,f217])).

fof(f204,plain,(
    ! [X6] :
      ( k9_relat_1(sK2,k10_relat_1(sK2,X6)) = X6
      | ~ r1_tarski(X6,k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f200,f54])).

fof(f200,plain,(
    ! [X6] :
      ( k9_relat_1(sK2,k10_relat_1(sK2,X6)) = X6
      | ~ r1_tarski(X6,k2_relat_1(sK2))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f157,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f849,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f848,f60])).

fof(f848,plain,(
    k2_subset_1(k1_relat_1(sK2)) = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k2_subset_1(k1_relat_1(sK2)))) ),
    inference(resolution,[],[f567,f61])).

fof(f567,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_relat_1(sK2)))
      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X1)) = X1 ) ),
    inference(resolution,[],[f190,f79])).

fof(f190,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK2))
      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f189,f157])).

fof(f189,plain,(
    ! [X1] :
      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f186,f54])).

fof(f186,plain,(
    ! [X1] :
      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f149,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

fof(f149,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f148,f57])).

fof(f148,plain,
    ( v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f130,f54])).

fof(f130,plain,
    ( v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f56,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f927,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k9_relat_1(k2_funct_1(sK2),sK0) ),
    inference(superposition,[],[f330,f573])).

fof(f573,plain,(
    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f570,f301])).

fof(f570,plain,
    ( k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f401,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f401,plain,(
    r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK0) ),
    inference(subsumption_resolution,[],[f400,f301])).

fof(f400,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f302,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f302,plain,(
    v4_relat_1(k2_funct_1(sK2),sK0) ),
    inference(resolution,[],[f121,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f330,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(k2_funct_1(sK2),X2)) = k9_relat_1(k2_funct_1(sK2),X2) ),
    inference(resolution,[],[f301,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f552,plain,(
    ~ r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f547])).

fof(f547,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f356,f543])).

fof(f543,plain,(
    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f220,f58])).

fof(f356,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | ~ r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f355,f157])).

fof(f355,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f354,f54])).

fof(f354,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f353,f149])).

fof(f353,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | ~ v2_funct_1(sK2)
    | ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f352])).

fof(f352,plain,
    ( sK1 != sK1
    | sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | ~ v2_funct_1(sK2)
    | ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f192,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f192,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f191,f57])).

fof(f191,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f184,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f184,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f183,f163])).

fof(f163,plain,(
    ! [X1] : k7_relset_1(sK0,sK0,sK2,X1) = k9_relat_1(sK2,X1) ),
    inference(resolution,[],[f57,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f183,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f182,f163])).

fof(f182,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f59,f162])).

fof(f162,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0) ),
    inference(resolution,[],[f57,f87])).

fof(f59,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.33  % Computer   : n015.cluster.edu
% 0.15/0.33  % Model      : x86_64 x86_64
% 0.15/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.33  % Memory     : 8042.1875MB
% 0.15/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.33  % CPULimit   : 60
% 0.15/0.33  % WCLimit    : 600
% 0.15/0.33  % DateTime   : Tue Dec  1 14:35:23 EST 2020
% 0.15/0.33  % CPUTime    : 
% 0.20/0.43  % (10193)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (10199)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.46  % (10185)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (10194)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (10192)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (10186)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (10189)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (10181)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (10195)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (10188)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.50  % (10183)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (10182)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (10184)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (10180)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (10190)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (10190)Refutation not found, incomplete strategy% (10190)------------------------------
% 0.20/0.50  % (10190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (10190)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (10190)Memory used [KB]: 6140
% 0.20/0.50  % (10190)Time elapsed: 0.101 s
% 0.20/0.50  % (10190)------------------------------
% 0.20/0.50  % (10190)------------------------------
% 0.20/0.51  % (10191)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (10197)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (10196)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (10187)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.51  % (10198)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (10200)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.52  % (10200)Refutation not found, incomplete strategy% (10200)------------------------------
% 0.20/0.52  % (10200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10200)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10200)Memory used [KB]: 10618
% 0.20/0.52  % (10200)Time elapsed: 0.115 s
% 0.20/0.52  % (10200)------------------------------
% 0.20/0.52  % (10200)------------------------------
% 0.20/0.54  % (10184)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f973,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f946,f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    r1_tarski(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    (sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 0.20/0.54    inference(flattening,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.20/0.54    inference(negated_conjecture,[],[f21])).
% 0.20/0.54  fof(f21,conjecture,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).
% 0.20/0.54  fof(f946,plain,(
% 0.20/0.54    ~r1_tarski(sK1,sK0)),
% 0.20/0.54    inference(backward_demodulation,[],[f552,f930])).
% 0.20/0.54  fof(f930,plain,(
% 0.20/0.54    sK0 = k1_relat_1(sK2)),
% 0.20/0.54    inference(forward_demodulation,[],[f929,f392])).
% 0.20/0.54  fof(f392,plain,(
% 0.20/0.54    sK0 = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f391,f301])).
% 0.20/0.54  fof(f301,plain,(
% 0.20/0.54    v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(resolution,[],[f121,f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.54    inference(backward_demodulation,[],[f117,f120])).
% 0.20/0.54  fof(f120,plain,(
% 0.20/0.54    k2_funct_1(sK2) = k2_funct_2(sK0,sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f119,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    v1_funct_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f50])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f118,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    v3_funct_2(sK2,sK0,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f50])).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f105,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.54    inference(cnf_transformation,[],[f50])).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    k2_funct_1(sK2) = k2_funct_2(sK0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f55,f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.54    inference(flattening,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    v1_funct_2(sK2,sK0,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f50])).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.54    inference(subsumption_resolution,[],[f116,f54])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f115,f56])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f104,f57])).
% 0.20/0.54  fof(f104,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f55,f74])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.54    inference(flattening,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.20/0.54  fof(f391,plain,(
% 0.20/0.54    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f390,f303])).
% 0.20/0.54  fof(f303,plain,(
% 0.20/0.54    v5_relat_1(k2_funct_1(sK2),sK0)),
% 0.20/0.54    inference(resolution,[],[f121,f83])).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.54  fof(f390,plain,(
% 0.20/0.54    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v5_relat_1(k2_funct_1(sK2),sK0) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(resolution,[],[f265,f77])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.20/0.54  fof(f265,plain,(
% 0.20/0.54    v2_funct_2(k2_funct_1(sK2),sK0)),
% 0.20/0.54    inference(subsumption_resolution,[],[f264,f121])).
% 0.20/0.54  fof(f264,plain,(
% 0.20/0.54    v2_funct_2(k2_funct_1(sK2),sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.54    inference(subsumption_resolution,[],[f242,f124])).
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(backward_demodulation,[],[f108,f120])).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    v1_funct_1(k2_funct_2(sK0,sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f107,f54])).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    v1_funct_1(k2_funct_2(sK0,sK2)) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f106,f56])).
% 0.20/0.54  fof(f106,plain,(
% 0.20/0.54    v1_funct_1(k2_funct_2(sK0,sK2)) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f101,f57])).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    v1_funct_1(k2_funct_2(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f55,f71])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f242,plain,(
% 0.20/0.54    v2_funct_2(k2_funct_1(sK2),sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.54    inference(resolution,[],[f122,f86])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(flattening,[],[f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.20/0.54  fof(f122,plain,(
% 0.20/0.54    v3_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 0.20/0.54    inference(backward_demodulation,[],[f114,f120])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)),
% 0.20/0.54    inference(subsumption_resolution,[],[f113,f54])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f112,f56])).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f103,f57])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f55,f73])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f929,plain,(
% 0.20/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(forward_demodulation,[],[f927,f850])).
% 0.20/0.54  fof(f850,plain,(
% 0.20/0.54    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),sK0)),
% 0.20/0.54    inference(forward_demodulation,[],[f849,f808])).
% 0.20/0.54  fof(f808,plain,(
% 0.20/0.54    sK0 = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.20/0.54    inference(forward_demodulation,[],[f807,f221])).
% 0.20/0.54  fof(f221,plain,(
% 0.20/0.54    k1_relat_1(sK2) = k10_relat_1(sK2,sK0)),
% 0.20/0.54    inference(backward_demodulation,[],[f193,f217])).
% 0.20/0.54  fof(f217,plain,(
% 0.20/0.54    sK0 = k2_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f216,f157])).
% 0.20/0.54  fof(f157,plain,(
% 0.20/0.54    v1_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f57,f81])).
% 0.20/0.54  fof(f216,plain,(
% 0.20/0.54    sK0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f215,f159])).
% 0.20/0.54  fof(f159,plain,(
% 0.20/0.54    v5_relat_1(sK2,sK0)),
% 0.20/0.54    inference(resolution,[],[f57,f83])).
% 0.20/0.54  fof(f215,plain,(
% 0.20/0.54    sK0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f151,f77])).
% 0.20/0.54  fof(f151,plain,(
% 0.20/0.54    v2_funct_2(sK2,sK0)),
% 0.20/0.54    inference(subsumption_resolution,[],[f150,f57])).
% 0.20/0.54  fof(f150,plain,(
% 0.20/0.54    v2_funct_2(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.54    inference(subsumption_resolution,[],[f131,f54])).
% 0.20/0.54  fof(f131,plain,(
% 0.20/0.54    v2_funct_2(sK2,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.54    inference(resolution,[],[f56,f86])).
% 0.20/0.54  fof(f193,plain,(
% 0.20/0.54    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.20/0.54    inference(resolution,[],[f157,f62])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.54  fof(f807,plain,(
% 0.20/0.54    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.20/0.54    inference(forward_demodulation,[],[f803,f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.54  fof(f803,plain,(
% 0.20/0.54    k2_subset_1(sK0) = k9_relat_1(sK2,k10_relat_1(sK2,k2_subset_1(sK0)))),
% 0.20/0.54    inference(resolution,[],[f546,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.54  fof(f546,plain,(
% 0.20/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | k9_relat_1(sK2,k10_relat_1(sK2,X1)) = X1) )),
% 0.20/0.54    inference(resolution,[],[f220,f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.54  fof(f220,plain,(
% 0.20/0.54    ( ! [X6] : (~r1_tarski(X6,sK0) | k9_relat_1(sK2,k10_relat_1(sK2,X6)) = X6) )),
% 0.20/0.54    inference(backward_demodulation,[],[f204,f217])).
% 0.20/0.54  fof(f204,plain,(
% 0.20/0.54    ( ! [X6] : (k9_relat_1(sK2,k10_relat_1(sK2,X6)) = X6 | ~r1_tarski(X6,k2_relat_1(sK2))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f200,f54])).
% 0.20/0.54  fof(f200,plain,(
% 0.20/0.54    ( ! [X6] : (k9_relat_1(sK2,k10_relat_1(sK2,X6)) = X6 | ~r1_tarski(X6,k2_relat_1(sK2)) | ~v1_funct_1(sK2)) )),
% 0.20/0.54    inference(resolution,[],[f157,f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.54  fof(f849,plain,(
% 0.20/0.54    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2)))),
% 0.20/0.54    inference(forward_demodulation,[],[f848,f60])).
% 0.20/0.54  fof(f848,plain,(
% 0.20/0.54    k2_subset_1(k1_relat_1(sK2)) = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k2_subset_1(k1_relat_1(sK2))))),
% 0.20/0.54    inference(resolution,[],[f567,f61])).
% 0.20/0.54  fof(f567,plain,(
% 0.20/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_relat_1(sK2))) | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X1)) = X1) )),
% 0.20/0.54    inference(resolution,[],[f190,f79])).
% 0.20/0.54  fof(f190,plain,(
% 0.20/0.54    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK2)) | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X1)) = X1) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f189,f157])).
% 0.20/0.54  fof(f189,plain,(
% 0.20/0.54    ( ! [X1] : (k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f186,f54])).
% 0.20/0.54  fof(f186,plain,(
% 0.20/0.54    ( ! [X1] : (k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.54    inference(resolution,[],[f149,f64])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    v2_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f148,f57])).
% 0.20/0.54  fof(f148,plain,(
% 0.20/0.54    v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.54    inference(subsumption_resolution,[],[f130,f54])).
% 0.20/0.54  fof(f130,plain,(
% 0.20/0.54    v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.54    inference(resolution,[],[f56,f85])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f927,plain,(
% 0.20/0.54    k2_relat_1(k2_funct_1(sK2)) = k9_relat_1(k2_funct_1(sK2),sK0)),
% 0.20/0.54    inference(superposition,[],[f330,f573])).
% 0.20/0.54  fof(f573,plain,(
% 0.20/0.54    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),sK0)),
% 0.20/0.54    inference(subsumption_resolution,[],[f570,f301])).
% 0.20/0.54  fof(f570,plain,(
% 0.20/0.54    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),sK0) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(resolution,[],[f401,f67])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.54  fof(f401,plain,(
% 0.20/0.54    r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK0)),
% 0.20/0.54    inference(subsumption_resolution,[],[f400,f301])).
% 0.20/0.54  fof(f400,plain,(
% 0.20/0.54    r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK0) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(resolution,[],[f302,f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.54  fof(f302,plain,(
% 0.20/0.54    v4_relat_1(k2_funct_1(sK2),sK0)),
% 0.20/0.54    inference(resolution,[],[f121,f82])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f330,plain,(
% 0.20/0.54    ( ! [X2] : (k2_relat_1(k7_relat_1(k2_funct_1(sK2),X2)) = k9_relat_1(k2_funct_1(sK2),X2)) )),
% 0.20/0.54    inference(resolution,[],[f301,f66])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.54  fof(f552,plain,(
% 0.20/0.54    ~r1_tarski(sK1,k1_relat_1(sK2))),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f547])).
% 0.20/0.54  fof(f547,plain,(
% 0.20/0.54    sK1 != sK1 | ~r1_tarski(sK1,k1_relat_1(sK2))),
% 0.20/0.54    inference(backward_demodulation,[],[f356,f543])).
% 0.20/0.54  fof(f543,plain,(
% 0.20/0.54    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 0.20/0.54    inference(resolution,[],[f220,f58])).
% 0.20/0.54  fof(f356,plain,(
% 0.20/0.54    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | ~r1_tarski(sK1,k1_relat_1(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f355,f157])).
% 0.20/0.54  fof(f355,plain,(
% 0.20/0.54    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | ~r1_tarski(sK1,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f354,f54])).
% 0.20/0.54  fof(f354,plain,(
% 0.20/0.54    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | ~r1_tarski(sK1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f353,f149])).
% 0.20/0.54  fof(f353,plain,(
% 0.20/0.54    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | ~v2_funct_1(sK2) | ~r1_tarski(sK1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f352])).
% 0.20/0.54  fof(f352,plain,(
% 0.20/0.54    sK1 != sK1 | sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | ~v2_funct_1(sK2) | ~r1_tarski(sK1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(superposition,[],[f192,f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.20/0.54  fof(f192,plain,(
% 0.20/0.54    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f191,f57])).
% 0.20/0.54  fof(f191,plain,(
% 0.20/0.54    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.54    inference(superposition,[],[f184,f87])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.54  fof(f184,plain,(
% 0.20/0.54    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 0.20/0.54    inference(forward_demodulation,[],[f183,f163])).
% 0.20/0.54  fof(f163,plain,(
% 0.20/0.54    ( ! [X1] : (k7_relset_1(sK0,sK0,sK2,X1) = k9_relat_1(sK2,X1)) )),
% 0.20/0.54    inference(resolution,[],[f57,f88])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.54  fof(f183,plain,(
% 0.20/0.54    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 0.20/0.54    inference(backward_demodulation,[],[f182,f163])).
% 0.20/0.54  fof(f182,plain,(
% 0.20/0.54    sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 0.20/0.54    inference(backward_demodulation,[],[f59,f162])).
% 0.20/0.54  fof(f162,plain,(
% 0.20/0.54    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0)) )),
% 0.20/0.54    inference(resolution,[],[f57,f87])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.20/0.54    inference(cnf_transformation,[],[f50])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (10184)------------------------------
% 0.20/0.54  % (10184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10184)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (10184)Memory used [KB]: 2046
% 0.20/0.54  % (10184)Time elapsed: 0.141 s
% 0.20/0.54  % (10184)------------------------------
% 0.20/0.54  % (10184)------------------------------
% 0.20/0.54  % (10175)Success in time 0.195 s
%------------------------------------------------------------------------------
