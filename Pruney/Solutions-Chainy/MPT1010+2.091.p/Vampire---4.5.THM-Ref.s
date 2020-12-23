%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:04 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 135 expanded)
%              Number of leaves         :   13 (  33 expanded)
%              Depth                    :   20
%              Number of atoms          :  249 ( 588 expanded)
%              Number of equality atoms :   87 ( 167 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(subsumption_resolution,[],[f137,f80])).

fof(f80,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f137,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f130,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f130,plain,(
    r2_hidden(sK2,k1_xboole_0) ),
    inference(superposition,[],[f91,f124])).

fof(f124,plain,(
    k1_xboole_0 = k1_tarski(sK2) ),
    inference(subsumption_resolution,[],[f121,f50])).

fof(f50,plain,(
    sK2 != k1_funct_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( sK2 != k1_funct_1(sK4,sK3)
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK2 != k1_funct_1(sK4,sK3)
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_2(sK4,sK1,k1_tarski(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f121,plain,
    ( k1_xboole_0 = k1_tarski(sK2)
    | sK2 = k1_funct_1(sK4,sK3) ),
    inference(resolution,[],[f116,f49])).

fof(f49,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f116,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = k1_tarski(sK2)
      | sK2 = k1_funct_1(sK4,X0) ) ),
    inference(resolution,[],[f115,f92])).

fof(f92,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

% (22930)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f115,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2))
      | k1_xboole_0 = k1_tarski(sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f111,f94])).

fof(f94,plain,(
    v5_relat_1(sK4,k1_tarski(sK2)) ),
    inference(resolution,[],[f48,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK4,X1)
      | k1_xboole_0 = k1_tarski(sK2)
      | r2_hidden(k1_funct_1(sK4,X0),X1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f109,f99])).

fof(f99,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f97,f79])).

fof(f79,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f97,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(resolution,[],[f48,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = k1_tarski(sK2)
      | r2_hidden(k1_funct_1(sK4,X0),X1)
      | ~ v5_relat_1(sK4,X1)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f108,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(X1))
      | r2_hidden(X2,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

fof(f108,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = k1_tarski(sK2) ) ),
    inference(subsumption_resolution,[],[f107,f99])).

fof(f107,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
      | ~ v1_relat_1(sK4)
      | k1_xboole_0 = k1_tarski(sK2) ) ),
    inference(subsumption_resolution,[],[f106,f46])).

fof(f46,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | k1_xboole_0 = k1_tarski(sK2) ) ),
    inference(superposition,[],[f74,f101])).

fof(f101,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = k1_tarski(sK2) ),
    inference(superposition,[],[f98,f95])).

fof(f95,plain,(
    k1_relset_1(sK1,k1_tarski(sK2),sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f48,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f98,plain,
    ( sK1 = k1_relset_1(sK1,k1_tarski(sK2),sK4)
    | k1_xboole_0 = k1_tarski(sK2) ),
    inference(subsumption_resolution,[],[f96,f47])).

fof(f47,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f96,plain,
    ( ~ v1_funct_2(sK4,sK1,k1_tarski(sK2))
    | k1_xboole_0 = k1_tarski(sK2)
    | sK1 = k1_relset_1(sK1,k1_tarski(sK2),sK4) ),
    inference(resolution,[],[f48,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f13])).

% (22935)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f91,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:31:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (22915)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.47  % (22915)Refutation not found, incomplete strategy% (22915)------------------------------
% 0.22/0.47  % (22915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (22915)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (22915)Memory used [KB]: 1663
% 0.22/0.47  % (22915)Time elapsed: 0.066 s
% 0.22/0.47  % (22915)------------------------------
% 0.22/0.47  % (22915)------------------------------
% 0.22/0.48  % (22942)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.49  % (22922)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (22914)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (22938)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (22938)Refutation not found, incomplete strategy% (22938)------------------------------
% 0.22/0.52  % (22938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22938)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22938)Memory used [KB]: 10746
% 0.22/0.52  % (22938)Time elapsed: 0.115 s
% 0.22/0.52  % (22938)------------------------------
% 0.22/0.52  % (22938)------------------------------
% 0.22/0.54  % (22921)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (22916)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (22937)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (22928)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (22918)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (22929)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (22925)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (22917)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (22936)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (22939)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (22933)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.56  % (22931)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.56  % (22926)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.30/0.56  % (22920)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.56  % (22943)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.56  % (22931)Refutation not found, incomplete strategy% (22931)------------------------------
% 1.30/0.56  % (22931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (22931)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.56  
% 1.30/0.56  % (22931)Memory used [KB]: 1791
% 1.30/0.56  % (22931)Time elapsed: 0.148 s
% 1.30/0.56  % (22931)------------------------------
% 1.30/0.56  % (22931)------------------------------
% 1.30/0.56  % (22943)Refutation not found, incomplete strategy% (22943)------------------------------
% 1.30/0.56  % (22943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (22943)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.56  
% 1.30/0.56  % (22943)Memory used [KB]: 1663
% 1.30/0.56  % (22943)Time elapsed: 0.146 s
% 1.30/0.56  % (22943)------------------------------
% 1.30/0.56  % (22943)------------------------------
% 1.30/0.56  % (22928)Refutation found. Thanks to Tanya!
% 1.30/0.56  % SZS status Theorem for theBenchmark
% 1.30/0.56  % SZS output start Proof for theBenchmark
% 1.30/0.56  fof(f138,plain,(
% 1.30/0.56    $false),
% 1.30/0.56    inference(subsumption_resolution,[],[f137,f80])).
% 1.30/0.56  fof(f80,plain,(
% 1.30/0.56    v1_xboole_0(k1_xboole_0)),
% 1.30/0.56    inference(cnf_transformation,[],[f2])).
% 1.30/0.56  fof(f2,axiom,(
% 1.30/0.56    v1_xboole_0(k1_xboole_0)),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.30/0.56  fof(f137,plain,(
% 1.30/0.56    ~v1_xboole_0(k1_xboole_0)),
% 1.30/0.56    inference(resolution,[],[f130,f76])).
% 1.30/0.56  fof(f76,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f28])).
% 1.30/0.56  fof(f28,plain,(
% 1.30/0.56    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.30/0.56    inference(ennf_transformation,[],[f16])).
% 1.30/0.56  fof(f16,plain,(
% 1.30/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.30/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 1.30/0.56  fof(f1,axiom,(
% 1.30/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.30/0.56  fof(f130,plain,(
% 1.30/0.56    r2_hidden(sK2,k1_xboole_0)),
% 1.30/0.56    inference(superposition,[],[f91,f124])).
% 1.30/0.56  fof(f124,plain,(
% 1.30/0.56    k1_xboole_0 = k1_tarski(sK2)),
% 1.30/0.56    inference(subsumption_resolution,[],[f121,f50])).
% 1.30/0.56  fof(f50,plain,(
% 1.30/0.56    sK2 != k1_funct_1(sK4,sK3)),
% 1.30/0.56    inference(cnf_transformation,[],[f34])).
% 1.30/0.56  fof(f34,plain,(
% 1.30/0.56    sK2 != k1_funct_1(sK4,sK3) & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)),
% 1.30/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f33])).
% 1.30/0.56  fof(f33,plain,(
% 1.30/0.56    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK2 != k1_funct_1(sK4,sK3) & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4))),
% 1.30/0.56    introduced(choice_axiom,[])).
% 1.30/0.56  fof(f19,plain,(
% 1.30/0.56    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.30/0.56    inference(flattening,[],[f18])).
% 1.30/0.56  fof(f18,plain,(
% 1.30/0.56    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.30/0.56    inference(ennf_transformation,[],[f15])).
% 1.30/0.56  fof(f15,negated_conjecture,(
% 1.30/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.30/0.56    inference(negated_conjecture,[],[f14])).
% 1.30/0.56  fof(f14,conjecture,(
% 1.30/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.30/0.56  fof(f121,plain,(
% 1.30/0.56    k1_xboole_0 = k1_tarski(sK2) | sK2 = k1_funct_1(sK4,sK3)),
% 1.30/0.56    inference(resolution,[],[f116,f49])).
% 1.30/0.56  fof(f49,plain,(
% 1.30/0.56    r2_hidden(sK3,sK1)),
% 1.30/0.56    inference(cnf_transformation,[],[f34])).
% 1.30/0.56  fof(f116,plain,(
% 1.30/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = k1_tarski(sK2) | sK2 = k1_funct_1(sK4,X0)) )),
% 1.30/0.56    inference(resolution,[],[f115,f92])).
% 1.30/0.56  fof(f92,plain,(
% 1.30/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.30/0.56    inference(equality_resolution,[],[f68])).
% 1.30/0.56  fof(f68,plain,(
% 1.30/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.30/0.56    inference(cnf_transformation,[],[f45])).
% 1.30/0.56  fof(f45,plain,(
% 1.30/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.30/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 1.30/0.56  fof(f44,plain,(
% 1.30/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 1.30/0.56    introduced(choice_axiom,[])).
% 1.30/0.56  fof(f43,plain,(
% 1.30/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.30/0.56    inference(rectify,[],[f42])).
% 1.30/0.56  fof(f42,plain,(
% 1.30/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.30/0.56    inference(nnf_transformation,[],[f4])).
% 1.30/0.56  fof(f4,axiom,(
% 1.30/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.30/0.56  % (22930)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.30/0.56  fof(f115,plain,(
% 1.30/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2)) | k1_xboole_0 = k1_tarski(sK2) | ~r2_hidden(X0,sK1)) )),
% 1.30/0.56    inference(resolution,[],[f111,f94])).
% 1.30/0.56  fof(f94,plain,(
% 1.30/0.56    v5_relat_1(sK4,k1_tarski(sK2))),
% 1.30/0.56    inference(resolution,[],[f48,f77])).
% 1.30/0.56  fof(f77,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f29])).
% 1.30/0.56  fof(f29,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.56    inference(ennf_transformation,[],[f17])).
% 1.30/0.56  fof(f17,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.30/0.56    inference(pure_predicate_removal,[],[f11])).
% 1.30/0.56  fof(f11,axiom,(
% 1.30/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.30/0.56  fof(f48,plain,(
% 1.30/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 1.30/0.56    inference(cnf_transformation,[],[f34])).
% 1.30/0.56  fof(f111,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~v5_relat_1(sK4,X1) | k1_xboole_0 = k1_tarski(sK2) | r2_hidden(k1_funct_1(sK4,X0),X1) | ~r2_hidden(X0,sK1)) )),
% 1.30/0.56    inference(subsumption_resolution,[],[f109,f99])).
% 1.30/0.56  fof(f99,plain,(
% 1.30/0.56    v1_relat_1(sK4)),
% 1.30/0.56    inference(subsumption_resolution,[],[f97,f79])).
% 1.30/0.56  fof(f79,plain,(
% 1.30/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.30/0.56    inference(cnf_transformation,[],[f8])).
% 1.30/0.56  fof(f8,axiom,(
% 1.30/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.30/0.56  fof(f97,plain,(
% 1.30/0.56    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))),
% 1.30/0.56    inference(resolution,[],[f48,f78])).
% 1.30/0.56  fof(f78,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f30])).
% 1.30/0.56  fof(f30,plain,(
% 1.30/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.30/0.56    inference(ennf_transformation,[],[f7])).
% 1.30/0.56  fof(f7,axiom,(
% 1.30/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.30/0.56  fof(f109,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | k1_xboole_0 = k1_tarski(sK2) | r2_hidden(k1_funct_1(sK4,X0),X1) | ~v5_relat_1(sK4,X1) | ~v1_relat_1(sK4)) )),
% 1.30/0.56    inference(resolution,[],[f108,f75])).
% 1.30/0.56  fof(f75,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(X1)) | r2_hidden(X2,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f27])).
% 1.30/0.56  fof(f27,plain,(
% 1.30/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.30/0.56    inference(flattening,[],[f26])).
% 1.30/0.56  fof(f26,plain,(
% 1.30/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.30/0.56    inference(ennf_transformation,[],[f9])).
% 1.30/0.56  fof(f9,axiom,(
% 1.30/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).
% 1.30/0.56  fof(f108,plain,(
% 1.30/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) | ~r2_hidden(X0,sK1) | k1_xboole_0 = k1_tarski(sK2)) )),
% 1.30/0.56    inference(subsumption_resolution,[],[f107,f99])).
% 1.30/0.56  fof(f107,plain,(
% 1.30/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) | ~v1_relat_1(sK4) | k1_xboole_0 = k1_tarski(sK2)) )),
% 1.30/0.56    inference(subsumption_resolution,[],[f106,f46])).
% 1.30/0.56  fof(f46,plain,(
% 1.30/0.56    v1_funct_1(sK4)),
% 1.30/0.56    inference(cnf_transformation,[],[f34])).
% 1.30/0.56  fof(f106,plain,(
% 1.30/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_xboole_0 = k1_tarski(sK2)) )),
% 1.30/0.56    inference(superposition,[],[f74,f101])).
% 1.30/0.56  fof(f101,plain,(
% 1.30/0.56    sK1 = k1_relat_1(sK4) | k1_xboole_0 = k1_tarski(sK2)),
% 1.30/0.56    inference(superposition,[],[f98,f95])).
% 1.30/0.56  fof(f95,plain,(
% 1.30/0.56    k1_relset_1(sK1,k1_tarski(sK2),sK4) = k1_relat_1(sK4)),
% 1.30/0.56    inference(resolution,[],[f48,f67])).
% 1.30/0.56  fof(f67,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f23])).
% 1.30/0.56  fof(f23,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.56    inference(ennf_transformation,[],[f12])).
% 1.30/0.56  fof(f12,axiom,(
% 1.30/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.30/0.56  fof(f98,plain,(
% 1.30/0.56    sK1 = k1_relset_1(sK1,k1_tarski(sK2),sK4) | k1_xboole_0 = k1_tarski(sK2)),
% 1.30/0.56    inference(subsumption_resolution,[],[f96,f47])).
% 1.30/0.56  fof(f47,plain,(
% 1.30/0.56    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 1.30/0.56    inference(cnf_transformation,[],[f34])).
% 1.30/0.56  fof(f96,plain,(
% 1.30/0.56    ~v1_funct_2(sK4,sK1,k1_tarski(sK2)) | k1_xboole_0 = k1_tarski(sK2) | sK1 = k1_relset_1(sK1,k1_tarski(sK2),sK4)),
% 1.30/0.56    inference(resolution,[],[f48,f61])).
% 1.30/0.56  fof(f61,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.30/0.56    inference(cnf_transformation,[],[f41])).
% 1.30/0.56  fof(f41,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.56    inference(nnf_transformation,[],[f22])).
% 1.30/0.56  fof(f22,plain,(
% 1.30/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.56    inference(flattening,[],[f21])).
% 1.30/0.56  fof(f21,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.56    inference(ennf_transformation,[],[f13])).
% 1.30/0.56  % (22935)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.30/0.56  fof(f13,axiom,(
% 1.30/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.30/0.56  fof(f74,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f25])).
% 1.30/0.56  fof(f25,plain,(
% 1.30/0.56    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.30/0.56    inference(flattening,[],[f24])).
% 1.30/0.56  fof(f24,plain,(
% 1.30/0.56    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.30/0.56    inference(ennf_transformation,[],[f10])).
% 1.30/0.56  fof(f10,axiom,(
% 1.30/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 1.30/0.56  fof(f91,plain,(
% 1.30/0.56    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.30/0.56    inference(equality_resolution,[],[f90])).
% 1.30/0.56  fof(f90,plain,(
% 1.30/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.30/0.56    inference(equality_resolution,[],[f69])).
% 1.30/0.56  fof(f69,plain,(
% 1.30/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.30/0.56    inference(cnf_transformation,[],[f45])).
% 1.30/0.56  % SZS output end Proof for theBenchmark
% 1.30/0.56  % (22928)------------------------------
% 1.30/0.56  % (22928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (22928)Termination reason: Refutation
% 1.30/0.56  
% 1.30/0.56  % (22928)Memory used [KB]: 1791
% 1.30/0.56  % (22928)Time elapsed: 0.126 s
% 1.30/0.56  % (22928)------------------------------
% 1.30/0.56  % (22928)------------------------------
% 1.30/0.56  % (22905)Success in time 0.195 s
%------------------------------------------------------------------------------
