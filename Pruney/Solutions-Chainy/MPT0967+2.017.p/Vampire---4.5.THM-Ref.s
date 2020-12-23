%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 245 expanded)
%              Number of leaves         :   13 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  304 (1592 expanded)
%              Number of equality atoms :   81 ( 416 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f311,plain,(
    $false ),
    inference(subsumption_resolution,[],[f310,f240])).

fof(f240,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f239,f128])).

fof(f128,plain,
    ( k1_xboole_0 != sK1
    | v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f40,f118])).

fof(f118,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f117,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f117,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 != sK1 ),
    inference(resolution,[],[f58,f92])).

fof(f92,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | k1_xboole_0 != sK1 ),
    inference(resolution,[],[f59,f86])).

fof(f86,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != sK1 ),
    inference(forward_demodulation,[],[f84,f77])).

fof(f77,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f84,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_xboole_0 != sK1 ),
    inference(superposition,[],[f42,f44])).

fof(f44,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f32])).

% (12225)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f239,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != sK1 ),
    inference(resolution,[],[f151,f141])).

fof(f141,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 != sK1 ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 != sK1
    | k1_xboole_0 != sK1 ),
    inference(superposition,[],[f90,f118])).

fof(f90,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f89,f86])).

fof(f89,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | k1_xboole_0 != sK1 ),
    inference(forward_demodulation,[],[f88,f77])).

fof(f88,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f87,f40])).

fof(f87,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 != sK1 ),
    inference(superposition,[],[f45,f44])).

fof(f45,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f151,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f150,f49])).

fof(f150,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f149,f48])).

fof(f48,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f149,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f148,f100])).

fof(f100,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f64,f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f148,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f54,f47])).

fof(f47,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f310,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f304,f43])).

fof(f43,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

% (12216)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f304,plain,
    ( ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f301,f217])).

fof(f217,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),X0)
      | ~ r1_tarski(X0,sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f215,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f215,plain,
    ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f214,f176])).

fof(f176,plain,(
    ! [X15] :
      ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),X15)
      | k1_xboole_0 = sK1
      | v1_funct_2(sK3,sK0,X15) ) ),
    inference(subsumption_resolution,[],[f175,f40])).

fof(f175,plain,(
    ! [X15] :
      ( k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),X15)
      | v1_funct_2(sK3,sK0,X15)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f170,f41])).

fof(f41,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f170,plain,(
    ! [X15] :
      ( k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),X15)
      | v1_funct_2(sK3,sK0,X15)
      | ~ v1_funct_2(sK3,sK0,sK1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f70,f42])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | v1_funct_2(X3,X0,X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f214,plain,
    ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(subsumption_resolution,[],[f208,f41])).

fof(f208,plain,
    ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(resolution,[],[f188,f42])).

fof(f188,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ r1_tarski(k2_relset_1(sK0,X0,sK3),sK2)
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK3,sK0,X0)
      | ~ v1_funct_2(sK3,sK0,sK2) ) ),
    inference(subsumption_resolution,[],[f187,f40])).

fof(f187,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(k2_relset_1(sK0,X0,sK3),sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_funct_2(sK3,sK0,X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,sK0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(k2_relset_1(sK0,X0,sK3),sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_funct_2(sK3,sK0,X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f72,f45])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f301,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK1) ),
    inference(resolution,[],[f154,f42])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k2_relset_1(X1,X2,X0),X2) ) ),
    inference(resolution,[],[f65,f59])).

% (12220)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:02:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (12203)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.48  % (12210)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.49  % (12218)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (12204)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (12223)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (12200)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (12200)Refutation not found, incomplete strategy% (12200)------------------------------
% 0.21/0.51  % (12200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12200)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12200)Memory used [KB]: 1663
% 0.21/0.51  % (12200)Time elapsed: 0.105 s
% 0.21/0.51  % (12200)------------------------------
% 0.21/0.51  % (12200)------------------------------
% 0.21/0.51  % (12215)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (12211)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (12222)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (12201)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (12217)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (12199)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (12206)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (12227)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (12209)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (12219)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (12214)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (12224)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (12207)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (12228)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (12221)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (12209)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (12202)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f311,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f310,f240])).
% 0.21/0.54  fof(f240,plain,(
% 0.21/0.54    k1_xboole_0 != sK1),
% 0.21/0.54    inference(subsumption_resolution,[],[f239,f128])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | v1_funct_1(k1_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f40,f118])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    k1_xboole_0 = sK3 | k1_xboole_0 != sK1),
% 0.21/0.54    inference(subsumption_resolution,[],[f117,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    k1_xboole_0 = sK3 | ~r1_tarski(k1_xboole_0,sK3) | k1_xboole_0 != sK1),
% 0.21/0.54    inference(resolution,[],[f58,f92])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    r1_tarski(sK3,k1_xboole_0) | k1_xboole_0 != sK1),
% 0.21/0.54    inference(resolution,[],[f59,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != sK1),
% 0.21/0.54    inference(forward_demodulation,[],[f84,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.54    inference(flattening,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | k1_xboole_0 != sK1),
% 0.21/0.54    inference(superposition,[],[f42,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f32])).
% 0.21/0.54  % (12225)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.54    inference(negated_conjecture,[],[f16])).
% 0.21/0.54  fof(f16,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    v1_funct_1(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f239,plain,(
% 0.21/0.54    ~v1_funct_1(k1_xboole_0) | k1_xboole_0 != sK1),
% 0.21/0.54    inference(resolution,[],[f151,f141])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 != sK1),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f134])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 != sK1 | k1_xboole_0 != sK1),
% 0.21/0.54    inference(superposition,[],[f90,f118])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ~v1_funct_2(sK3,k1_xboole_0,sK2) | k1_xboole_0 != sK1),
% 0.21/0.54    inference(subsumption_resolution,[],[f89,f86])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK3,k1_xboole_0,sK2) | k1_xboole_0 != sK1),
% 0.21/0.54    inference(forward_demodulation,[],[f88,f77])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~v1_funct_2(sK3,k1_xboole_0,sK2) | k1_xboole_0 != sK1),
% 0.21/0.54    inference(subsumption_resolution,[],[f87,f40])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~v1_funct_1(sK3) | k1_xboole_0 != sK1),
% 0.21/0.54    inference(superposition,[],[f45,f44])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f150,f49])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f149,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_funct_1(k1_xboole_0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f148,f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    v1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(resolution,[],[f64,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f54,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.54  fof(f310,plain,(
% 0.21/0.54    k1_xboole_0 = sK1),
% 0.21/0.54    inference(subsumption_resolution,[],[f304,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    r1_tarski(sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  % (12216)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  fof(f304,plain,(
% 0.21/0.54    ~r1_tarski(sK1,sK2) | k1_xboole_0 = sK1),
% 0.21/0.54    inference(resolution,[],[f301,f217])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k2_relset_1(sK0,sK1,sK3),X0) | ~r1_tarski(X0,sK2) | k1_xboole_0 = sK1) )),
% 0.21/0.54    inference(resolution,[],[f215,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    ~r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) | k1_xboole_0 = sK1),
% 0.21/0.54    inference(subsumption_resolution,[],[f214,f176])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    ( ! [X15] : (~r1_tarski(k2_relset_1(sK0,sK1,sK3),X15) | k1_xboole_0 = sK1 | v1_funct_2(sK3,sK0,X15)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f175,f40])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ( ! [X15] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK0,sK1,sK3),X15) | v1_funct_2(sK3,sK0,X15) | ~v1_funct_1(sK3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f170,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    ( ! [X15] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK0,sK1,sK3),X15) | v1_funct_2(sK3,sK0,X15) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3)) )),
% 0.21/0.54    inference(resolution,[],[f70,f42])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | v1_funct_2(X3,X0,X2) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    ~r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f208,f41])).
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    ~r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_2(sK3,sK0,sK2)),
% 0.21/0.54    inference(resolution,[],[f188,f42])).
% 0.21/0.54  fof(f188,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~r1_tarski(k2_relset_1(sK0,X0,sK3),sK2) | k1_xboole_0 = X0 | ~v1_funct_2(sK3,sK0,X0) | ~v1_funct_2(sK3,sK0,sK2)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f187,f40])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(k2_relset_1(sK0,X0,sK3),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_2(sK3,sK0,X0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f179])).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(k2_relset_1(sK0,X0,sK3),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_2(sK3,sK0,X0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) )),
% 0.21/0.54    inference(resolution,[],[f72,f45])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f301,plain,(
% 0.21/0.54    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK1)),
% 0.21/0.54    inference(resolution,[],[f154,f42])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k2_relset_1(X1,X2,X0),X2)) )),
% 0.21/0.54    inference(resolution,[],[f65,f59])).
% 0.21/0.54  % (12220)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (12209)------------------------------
% 0.21/0.54  % (12209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12209)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (12209)Memory used [KB]: 1791
% 0.21/0.54  % (12209)Time elapsed: 0.139 s
% 0.21/0.54  % (12209)------------------------------
% 0.21/0.54  % (12209)------------------------------
% 0.21/0.54  % (12195)Success in time 0.185 s
%------------------------------------------------------------------------------
