%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:10 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  118 (8869 expanded)
%              Number of leaves         :   14 (2213 expanded)
%              Depth                    :   24
%              Number of atoms          :  329 (59534 expanded)
%              Number of equality atoms :   88 (13098 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1259,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1258,f1030])).

fof(f1030,plain,(
    ! [X0] : v1_funct_2(k7_relat_1(sK3,X0),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f887,f1013])).

fof(f1013,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(backward_demodulation,[],[f152,f992])).

fof(f992,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f503,f965])).

fof(f965,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f107,f940])).

fof(f940,plain,(
    sK3 = k7_relat_1(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f114,f934])).

fof(f934,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f867,f46])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

% (25884)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (25883)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (25872)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f867,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f121,f574,f864])).

fof(f864,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f737,f573])).

fof(f573,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f300,f45])).

fof(f45,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f300,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k1_relat_1(k7_relat_1(sK3,X0)) = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f111,f166])).

fof(f166,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f105,f86])).

fof(f86,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f44,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f105,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f93,f43])).

fof(f43,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f44,f64])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f111,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_relat_1(sK3))
      | k1_relat_1(k7_relat_1(sK3,X3)) = X3 ) ),
    inference(resolution,[],[f85,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f85,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f44,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f737,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)) ),
    inference(unit_resulting_resolution,[],[f214,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f214,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1))) ),
    inference(unit_resulting_resolution,[],[f130,f101,f168,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f168,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(unit_resulting_resolution,[],[f130,f133,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f133,plain,(
    ! [X0] : v5_relat_1(k7_relat_1(sK3,X0),sK1) ),
    inference(unit_resulting_resolution,[],[f102,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f102,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f91,f89])).

fof(f89,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) ),
    inference(unit_resulting_resolution,[],[f42,f44,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f42,f44,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f101,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(backward_demodulation,[],[f90,f89])).

% (25882)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f90,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f42,f44,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f130,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f102,f60])).

fof(f574,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f213,f573])).

fof(f213,plain,(
    ! [X0] : v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(unit_resulting_resolution,[],[f130,f101,f168,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f121,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    inference(subsumption_resolution,[],[f120,f101])).

fof(f120,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1)) ),
    inference(resolution,[],[f104,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f104,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k7_relat_1(sK3,sK2)) ),
    inference(forward_demodulation,[],[f103,f89])).

fof(f103,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    inference(forward_demodulation,[],[f100,f89])).

fof(f100,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    inference(backward_demodulation,[],[f47,f89])).

fof(f47,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,(
    sK3 = k7_relat_1(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f85,f87,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f87,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f44,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f107,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f48,f85,f51])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f503,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f130,f471,f57])).

fof(f471,plain,(
    ! [X0] : v4_relat_1(k7_relat_1(sK3,X0),k1_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f266,f62])).

fof(f266,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) ),
    inference(backward_demodulation,[],[f253,f251])).

fof(f251,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(k1_relat_1(sK3),sK1,sK3,X0) ),
    inference(unit_resulting_resolution,[],[f42,f123,f70])).

fof(f123,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) ),
    inference(unit_resulting_resolution,[],[f85,f42,f115,f56])).

fof(f115,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f85,f88,f52])).

fof(f88,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f44,f63])).

fof(f253,plain,(
    ! [X0] : m1_subset_1(k2_partfun1(k1_relat_1(sK3),sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) ),
    inference(unit_resulting_resolution,[],[f42,f123,f72])).

fof(f152,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f48,f130,f51])).

fof(f887,plain,(
    ! [X0] : v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f213,f867])).

fof(f1258,plain,(
    ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1257,f1240])).

fof(f1240,plain,(
    k1_xboole_0 = sK2 ),
    inference(unit_resulting_resolution,[],[f937,f1036])).

fof(f1036,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(backward_demodulation,[],[f978,f1013])).

fof(f978,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_relat_1(k7_relat_1(sK3,X3)) = X3 ) ),
    inference(backward_demodulation,[],[f111,f965])).

fof(f937,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f45,f934])).

fof(f1257,plain,(
    ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1245,f1031])).

fof(f1031,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f888,f1013])).

fof(f888,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f214,f867])).

fof(f1245,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f927,f1240])).

fof(f927,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f926,f867])).

fof(f926,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    inference(subsumption_resolution,[],[f875,f101])).

fof(f875,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k7_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f104,f867])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:07:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (25885)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (25877)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (25887)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (25879)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (25880)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (25888)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.46/0.56  % (25875)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.46/0.56  % (25874)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.46/0.56  % (25876)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.46/0.56  % (25889)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.46/0.56  % (25881)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.59/0.56  % (25873)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.57  % (25891)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.59/0.57  % (25890)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.59/0.57  % (25892)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.59/0.57  % (25887)Refutation found. Thanks to Tanya!
% 1.59/0.57  % SZS status Theorem for theBenchmark
% 1.59/0.57  % (25892)Refutation not found, incomplete strategy% (25892)------------------------------
% 1.59/0.57  % (25892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (25892)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (25892)Memory used [KB]: 10618
% 1.59/0.57  % (25892)Time elapsed: 0.135 s
% 1.59/0.57  % (25892)------------------------------
% 1.59/0.57  % (25892)------------------------------
% 1.59/0.57  % SZS output start Proof for theBenchmark
% 1.59/0.57  fof(f1259,plain,(
% 1.59/0.57    $false),
% 1.59/0.57    inference(subsumption_resolution,[],[f1258,f1030])).
% 1.59/0.57  fof(f1030,plain,(
% 1.59/0.57    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,X0),k1_xboole_0,k1_xboole_0)) )),
% 1.59/0.57    inference(backward_demodulation,[],[f887,f1013])).
% 1.59/0.57  fof(f1013,plain,(
% 1.59/0.57    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.59/0.57    inference(backward_demodulation,[],[f152,f992])).
% 1.59/0.57  fof(f992,plain,(
% 1.59/0.57    ( ! [X0] : (k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),k1_xboole_0)) )),
% 1.59/0.57    inference(backward_demodulation,[],[f503,f965])).
% 1.59/0.57  fof(f965,plain,(
% 1.59/0.57    k1_xboole_0 = k1_relat_1(sK3)),
% 1.59/0.57    inference(backward_demodulation,[],[f107,f940])).
% 1.59/0.57  fof(f940,plain,(
% 1.59/0.57    sK3 = k7_relat_1(sK3,k1_xboole_0)),
% 1.59/0.57    inference(backward_demodulation,[],[f114,f934])).
% 1.59/0.57  fof(f934,plain,(
% 1.59/0.57    k1_xboole_0 = sK0),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f867,f46])).
% 1.59/0.57  fof(f46,plain,(
% 1.59/0.57    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.59/0.57    inference(cnf_transformation,[],[f38])).
% 1.59/0.57  fof(f38,plain,(
% 1.59/0.57    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.59/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f37])).
% 1.59/0.57  fof(f37,plain,(
% 1.59/0.57    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.59/0.57    introduced(choice_axiom,[])).
% 1.59/0.57  fof(f18,plain,(
% 1.59/0.57    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.59/0.57    inference(flattening,[],[f17])).
% 1.59/0.57  fof(f17,plain,(
% 1.59/0.57    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.59/0.57    inference(ennf_transformation,[],[f16])).
% 1.59/0.57  fof(f16,negated_conjecture,(
% 1.59/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.59/0.57    inference(negated_conjecture,[],[f15])).
% 1.59/0.57  fof(f15,conjecture,(
% 1.59/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 1.59/0.57  % (25884)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.57  % (25883)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.59/0.57  % (25872)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.59/0.57  fof(f867,plain,(
% 1.59/0.57    k1_xboole_0 = sK1),
% 1.59/0.57    inference(global_subsumption,[],[f121,f574,f864])).
% 1.59/0.57  fof(f864,plain,(
% 1.59/0.57    r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1)) | k1_xboole_0 = sK1),
% 1.59/0.57    inference(superposition,[],[f737,f573])).
% 1.59/0.57  fof(f573,plain,(
% 1.59/0.57    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | k1_xboole_0 = sK1),
% 1.59/0.57    inference(resolution,[],[f300,f45])).
% 1.59/0.57  fof(f45,plain,(
% 1.59/0.57    r1_tarski(sK2,sK0)),
% 1.59/0.57    inference(cnf_transformation,[],[f38])).
% 1.59/0.57  fof(f300,plain,(
% 1.59/0.57    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0 | k1_xboole_0 = sK1) )),
% 1.59/0.57    inference(superposition,[],[f111,f166])).
% 1.59/0.57  fof(f166,plain,(
% 1.59/0.57    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.59/0.57    inference(superposition,[],[f105,f86])).
% 1.59/0.57  fof(f86,plain,(
% 1.59/0.57    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f44,f61])).
% 1.59/0.57  fof(f61,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f29])).
% 1.59/0.57  fof(f29,plain,(
% 1.59/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.57    inference(ennf_transformation,[],[f10])).
% 1.59/0.57  fof(f10,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.59/0.57  fof(f44,plain,(
% 1.59/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.59/0.57    inference(cnf_transformation,[],[f38])).
% 1.59/0.57  fof(f105,plain,(
% 1.59/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.59/0.57    inference(subsumption_resolution,[],[f93,f43])).
% 1.59/0.57  fof(f43,plain,(
% 1.59/0.57    v1_funct_2(sK3,sK0,sK1)),
% 1.59/0.57    inference(cnf_transformation,[],[f38])).
% 1.59/0.57  fof(f93,plain,(
% 1.59/0.57    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.59/0.57    inference(resolution,[],[f44,f64])).
% 1.59/0.57  fof(f64,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.59/0.57    inference(cnf_transformation,[],[f41])).
% 1.59/0.57  fof(f41,plain,(
% 1.59/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.57    inference(nnf_transformation,[],[f32])).
% 1.59/0.57  fof(f32,plain,(
% 1.59/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.57    inference(flattening,[],[f31])).
% 1.59/0.57  fof(f31,plain,(
% 1.59/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.57    inference(ennf_transformation,[],[f11])).
% 1.59/0.57  fof(f11,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.59/0.57  fof(f111,plain,(
% 1.59/0.57    ( ! [X3] : (~r1_tarski(X3,k1_relat_1(sK3)) | k1_relat_1(k7_relat_1(sK3,X3)) = X3) )),
% 1.59/0.57    inference(resolution,[],[f85,f51])).
% 1.59/0.57  fof(f51,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.59/0.57    inference(cnf_transformation,[],[f22])).
% 1.59/0.57  fof(f22,plain,(
% 1.59/0.57    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.59/0.57    inference(flattening,[],[f21])).
% 1.59/0.57  fof(f21,plain,(
% 1.59/0.57    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.59/0.57    inference(ennf_transformation,[],[f7])).
% 1.59/0.57  fof(f7,axiom,(
% 1.59/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.59/0.57  fof(f85,plain,(
% 1.59/0.57    v1_relat_1(sK3)),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f44,f60])).
% 1.59/0.57  fof(f60,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f28])).
% 1.59/0.57  fof(f28,plain,(
% 1.59/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.57    inference(ennf_transformation,[],[f8])).
% 1.59/0.57  fof(f8,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.59/0.57  fof(f737,plain,(
% 1.59/0.57    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1))) )),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f214,f58])).
% 1.59/0.57  fof(f58,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f40])).
% 1.59/0.57  fof(f40,plain,(
% 1.59/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.59/0.57    inference(nnf_transformation,[],[f2])).
% 1.59/0.57  fof(f2,axiom,(
% 1.59/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.59/0.57  fof(f214,plain,(
% 1.59/0.57    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))) )),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f130,f101,f168,f56])).
% 1.59/0.57  fof(f56,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f25])).
% 1.59/0.57  fof(f25,plain,(
% 1.59/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.59/0.57    inference(flattening,[],[f24])).
% 1.59/0.57  fof(f24,plain,(
% 1.59/0.57    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.59/0.57    inference(ennf_transformation,[],[f14])).
% 1.59/0.57  fof(f14,axiom,(
% 1.59/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.59/0.57  fof(f168,plain,(
% 1.59/0.57    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f130,f133,f52])).
% 1.59/0.57  fof(f52,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f39])).
% 1.59/0.57  fof(f39,plain,(
% 1.59/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.59/0.57    inference(nnf_transformation,[],[f23])).
% 1.59/0.57  fof(f23,plain,(
% 1.59/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.59/0.57    inference(ennf_transformation,[],[f4])).
% 1.59/0.57  fof(f4,axiom,(
% 1.59/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.59/0.57  fof(f133,plain,(
% 1.59/0.57    ( ! [X0] : (v5_relat_1(k7_relat_1(sK3,X0),sK1)) )),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f102,f63])).
% 1.59/0.57  fof(f63,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f30])).
% 1.59/0.57  fof(f30,plain,(
% 1.59/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.57    inference(ennf_transformation,[],[f9])).
% 1.59/0.57  fof(f9,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.59/0.57  fof(f102,plain,(
% 1.59/0.57    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.59/0.57    inference(backward_demodulation,[],[f91,f89])).
% 1.59/0.57  fof(f89,plain,(
% 1.59/0.57    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) )),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f42,f44,f70])).
% 1.59/0.57  fof(f70,plain,(
% 1.59/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f34])).
% 1.59/0.57  fof(f34,plain,(
% 1.59/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.59/0.57    inference(flattening,[],[f33])).
% 1.59/0.57  fof(f33,plain,(
% 1.59/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.59/0.57    inference(ennf_transformation,[],[f13])).
% 1.59/0.57  fof(f13,axiom,(
% 1.59/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.59/0.57  fof(f42,plain,(
% 1.59/0.57    v1_funct_1(sK3)),
% 1.59/0.57    inference(cnf_transformation,[],[f38])).
% 1.59/0.57  fof(f91,plain,(
% 1.59/0.57    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f42,f44,f72])).
% 1.59/0.57  fof(f72,plain,(
% 1.59/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f36])).
% 1.59/0.58  fof(f36,plain,(
% 1.59/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.59/0.58    inference(flattening,[],[f35])).
% 1.59/0.58  fof(f35,plain,(
% 1.59/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.59/0.58    inference(ennf_transformation,[],[f12])).
% 1.59/0.58  fof(f12,axiom,(
% 1.59/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.59/0.58  fof(f101,plain,(
% 1.59/0.58    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 1.59/0.58    inference(backward_demodulation,[],[f90,f89])).
% 1.59/0.58  % (25882)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.59/0.58  fof(f90,plain,(
% 1.59/0.58    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f42,f44,f71])).
% 1.59/0.58  fof(f71,plain,(
% 1.59/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f36])).
% 1.59/0.58  fof(f130,plain,(
% 1.59/0.58    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f102,f60])).
% 1.59/0.58  fof(f574,plain,(
% 1.59/0.58    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | k1_xboole_0 = sK1),
% 1.59/0.58    inference(superposition,[],[f213,f573])).
% 1.59/0.58  fof(f213,plain,(
% 1.59/0.58    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f130,f101,f168,f55])).
% 1.59/0.58  fof(f55,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f25])).
% 1.59/0.58  fof(f121,plain,(
% 1.59/0.58    ~r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1)) | ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 1.59/0.58    inference(subsumption_resolution,[],[f120,f101])).
% 1.59/0.58  fof(f120,plain,(
% 1.59/0.58    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1))),
% 1.59/0.58    inference(resolution,[],[f104,f59])).
% 1.59/0.58  fof(f59,plain,(
% 1.59/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f40])).
% 1.59/0.58  fof(f104,plain,(
% 1.59/0.58    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_1(k7_relat_1(sK3,sK2))),
% 1.59/0.58    inference(forward_demodulation,[],[f103,f89])).
% 1.59/0.58  fof(f103,plain,(
% 1.59/0.58    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.59/0.58    inference(forward_demodulation,[],[f100,f89])).
% 1.59/0.58  fof(f100,plain,(
% 1.59/0.58    ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.59/0.58    inference(backward_demodulation,[],[f47,f89])).
% 1.59/0.58  fof(f47,plain,(
% 1.59/0.58    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.59/0.58    inference(cnf_transformation,[],[f38])).
% 1.59/0.58  fof(f114,plain,(
% 1.59/0.58    sK3 = k7_relat_1(sK3,sK0)),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f85,f87,f57])).
% 1.59/0.58  fof(f57,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.59/0.58    inference(cnf_transformation,[],[f27])).
% 1.59/0.58  fof(f27,plain,(
% 1.59/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.59/0.58    inference(flattening,[],[f26])).
% 1.59/0.58  fof(f26,plain,(
% 1.59/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.59/0.58    inference(ennf_transformation,[],[f5])).
% 1.59/0.58  fof(f5,axiom,(
% 1.59/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.59/0.58  fof(f87,plain,(
% 1.59/0.58    v4_relat_1(sK3,sK0)),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f44,f62])).
% 1.59/0.58  fof(f62,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f30])).
% 1.59/0.58  fof(f107,plain,(
% 1.59/0.58    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f48,f85,f51])).
% 1.59/0.58  fof(f48,plain,(
% 1.59/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f1])).
% 1.59/0.58  fof(f1,axiom,(
% 1.59/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.59/0.58  fof(f503,plain,(
% 1.59/0.58    ( ! [X0] : (k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(sK3))) )),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f130,f471,f57])).
% 1.59/0.58  fof(f471,plain,(
% 1.59/0.58    ( ! [X0] : (v4_relat_1(k7_relat_1(sK3,X0),k1_relat_1(sK3))) )),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f266,f62])).
% 1.59/0.58  fof(f266,plain,(
% 1.59/0.58    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))) )),
% 1.59/0.58    inference(backward_demodulation,[],[f253,f251])).
% 1.59/0.58  fof(f251,plain,(
% 1.59/0.58    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(k1_relat_1(sK3),sK1,sK3,X0)) )),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f42,f123,f70])).
% 1.59/0.58  fof(f123,plain,(
% 1.59/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f85,f42,f115,f56])).
% 1.59/0.58  fof(f115,plain,(
% 1.59/0.58    r1_tarski(k2_relat_1(sK3),sK1)),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f85,f88,f52])).
% 1.59/0.58  fof(f88,plain,(
% 1.59/0.58    v5_relat_1(sK3,sK1)),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f44,f63])).
% 1.59/0.58  fof(f253,plain,(
% 1.59/0.58    ( ! [X0] : (m1_subset_1(k2_partfun1(k1_relat_1(sK3),sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))) )),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f42,f123,f72])).
% 1.59/0.58  fof(f152,plain,(
% 1.59/0.58    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_xboole_0))) )),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f48,f130,f51])).
% 1.59/0.58  fof(f887,plain,(
% 1.59/0.58    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0)) )),
% 1.59/0.58    inference(backward_demodulation,[],[f213,f867])).
% 1.59/0.58  fof(f1258,plain,(
% 1.59/0.58    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 1.59/0.58    inference(forward_demodulation,[],[f1257,f1240])).
% 1.59/0.58  fof(f1240,plain,(
% 1.59/0.58    k1_xboole_0 = sK2),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f937,f1036])).
% 1.59/0.58  fof(f1036,plain,(
% 1.59/0.58    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 1.59/0.58    inference(backward_demodulation,[],[f978,f1013])).
% 1.59/0.58  fof(f978,plain,(
% 1.59/0.58    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_relat_1(k7_relat_1(sK3,X3)) = X3) )),
% 1.59/0.58    inference(backward_demodulation,[],[f111,f965])).
% 1.59/0.58  fof(f937,plain,(
% 1.59/0.58    r1_tarski(sK2,k1_xboole_0)),
% 1.59/0.58    inference(backward_demodulation,[],[f45,f934])).
% 1.59/0.58  fof(f1257,plain,(
% 1.59/0.58    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f1245,f1031])).
% 1.59/0.58  fof(f1031,plain,(
% 1.59/0.58    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) )),
% 1.59/0.58    inference(backward_demodulation,[],[f888,f1013])).
% 1.59/0.58  fof(f888,plain,(
% 1.59/0.58    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0)))) )),
% 1.59/0.58    inference(backward_demodulation,[],[f214,f867])).
% 1.59/0.58  fof(f1245,plain,(
% 1.59/0.58    ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)),
% 1.59/0.58    inference(backward_demodulation,[],[f927,f1240])).
% 1.59/0.58  fof(f927,plain,(
% 1.59/0.58    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)),
% 1.59/0.58    inference(forward_demodulation,[],[f926,f867])).
% 1.59/0.58  fof(f926,plain,(
% 1.59/0.58    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 1.59/0.58    inference(subsumption_resolution,[],[f875,f101])).
% 1.59/0.58  fof(f875,plain,(
% 1.59/0.58    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_1(k7_relat_1(sK3,sK2))),
% 1.59/0.58    inference(backward_demodulation,[],[f104,f867])).
% 1.59/0.58  % SZS output end Proof for theBenchmark
% 1.59/0.58  % (25887)------------------------------
% 1.59/0.58  % (25887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (25887)Termination reason: Refutation
% 1.59/0.58  
% 1.59/0.58  % (25887)Memory used [KB]: 7036
% 1.59/0.58  % (25887)Time elapsed: 0.129 s
% 1.59/0.58  % (25887)------------------------------
% 1.59/0.58  % (25887)------------------------------
% 1.59/0.58  % (25871)Success in time 0.213 s
%------------------------------------------------------------------------------
