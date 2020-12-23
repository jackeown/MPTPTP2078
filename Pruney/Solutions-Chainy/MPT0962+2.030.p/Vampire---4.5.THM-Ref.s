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
% DateTime   : Thu Dec  3 13:00:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 576 expanded)
%              Number of leaves         :   14 ( 137 expanded)
%              Depth                    :   23
%              Number of atoms          :  304 (2598 expanded)
%              Number of equality atoms :  112 ( 483 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(subsumption_resolution,[],[f279,f165])).

fof(f165,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f164,f155])).

fof(f155,plain,(
    ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f152,f118])).

fof(f118,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f105,f115])).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 = sK5(X0,k1_xboole_0) ),
    inference(resolution,[],[f114,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f58,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f114,plain,(
    ! [X0] : r1_tarski(sK5(X0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f113,f85])).

fof(f85,plain,(
    ! [X0] : sP0(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(definition_folding,[],[f20,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f113,plain,(
    ! [X0] :
      ( r1_tarski(sK5(X0,k1_xboole_0),k1_xboole_0)
      | ~ sP0(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f108,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK5(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k2_relat_1(sK5(X0,X1)),X0)
        & k1_relat_1(sK5(X0,X1)) = X1
        & v1_funct_1(sK5(X0,X1))
        & v1_relat_1(sK5(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( r1_tarski(k2_relat_1(sK5(X0,X1)),X0)
        & k1_relat_1(sK5(X0,X1)) = X1
        & v1_funct_1(sK5(X0,X1))
        & v1_relat_1(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f108,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK5(X0,k1_xboole_0))
      | r1_tarski(sK5(X0,k1_xboole_0),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f107,f84])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f107,plain,(
    ! [X0] :
      ( r1_tarski(sK5(X0,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5(X0,k1_xboole_0))))
      | ~ v1_relat_1(sK5(X0,k1_xboole_0)) ) ),
    inference(superposition,[],[f54,f105])).

fof(f54,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(sK5(X0,k1_xboole_0)) ),
    inference(resolution,[],[f67,f85])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_relat_1(sK5(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f152,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f72,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f164,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f86,f136])).

fof(f136,plain,(
    ! [X0,X1] : sP1(X0,k1_xboole_0,X1) ),
    inference(resolution,[],[f77,f53])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f25,f30])).

% (28717)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f30,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f86,plain,(
    ! [X2,X1] :
      ( ~ sP1(k1_xboole_0,X1,X2)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1)
      | v1_funct_2(X1,k1_xboole_0,X2) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f279,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f271,f118])).

fof(f271,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f234,f268])).

fof(f268,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f267,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f267,plain,(
    sK3 = k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f266,f52])).

fof(f266,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f265,f83])).

fof(f265,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0),sK3)
    | sK3 = k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f263,f48])).

fof(f48,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
      | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
      | ~ v1_funct_1(sK3) )
    & r1_tarski(k2_relat_1(sK3),sK2)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
        | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
        | ~ v1_funct_1(sK3) )
      & r1_tarski(k2_relat_1(sK3),sK2)
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f263,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0),sK3)
    | sK3 = k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f101,f239])).

fof(f239,plain,(
    k1_xboole_0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f238,f52])).

fof(f238,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK3))
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f224,f222])).

fof(f222,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f221,f207])).

fof(f207,plain,(
    ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f91,f206])).

fof(f206,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(resolution,[],[f202,f50])).

fof(f50,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f202,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) ) ),
    inference(resolution,[],[f200,f81])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f200,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(k1_relat_1(sK3),X7)
      | ~ r1_tarski(k2_relat_1(sK3),X6)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X6))) ) ),
    inference(resolution,[],[f71,f48])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f91,plain,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(subsumption_resolution,[],[f51,f49])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f221,plain,
    ( k1_xboole_0 = sK2
    | v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f218,f208])).

fof(f208,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),sK2,sK3) ),
    inference(resolution,[],[f206,f72])).

fof(f218,plain,
    ( k1_relat_1(sK3) != k1_relset_1(k1_relat_1(sK3),sK2,sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    inference(resolution,[],[f75,f209])).

fof(f209,plain,(
    sP1(k1_relat_1(sK3),sK3,sK2) ),
    inference(resolution,[],[f206,f77])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 = X2
      | v1_funct_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f224,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f100,f222])).

fof(f100,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | sK2 = k2_relat_1(sK3) ),
    inference(resolution,[],[f58,f50])).

fof(f101,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)),X2)
      | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) = X2
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f58,f54])).

fof(f234,plain,(
    ~ v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) ),
    inference(backward_demodulation,[],[f207,f222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:21:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (28704)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.49  % (28705)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (28696)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (28697)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (28697)Refutation not found, incomplete strategy% (28697)------------------------------
% 0.21/0.50  % (28697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28697)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (28697)Memory used [KB]: 10746
% 0.21/0.50  % (28697)Time elapsed: 0.088 s
% 0.21/0.50  % (28697)------------------------------
% 0.21/0.50  % (28697)------------------------------
% 0.21/0.50  % (28696)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (28713)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.50  % (28701)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (28698)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (28706)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (28691)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (28712)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f279,f165])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f164,f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f152,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    inference(backward_demodulation,[],[f105,f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = sK5(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(resolution,[],[f114,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(resolution,[],[f58,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(sK5(X0,k1_xboole_0),k1_xboole_0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f113,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0] : (sP0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP0(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : (sP0(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.51    inference(definition_folding,[],[f20,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) | ~sP0(X0,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : (? [X2] : ((r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1) & (v1_funct_1(X2) & v1_relat_1(X2))) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(sK5(X0,k1_xboole_0),k1_xboole_0) | ~sP0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(resolution,[],[f108,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(sK5(X0,X1)) | ~sP0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(k2_relat_1(sK5(X0,X1)),X0) & k1_relat_1(sK5(X0,X1)) = X1 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))) | ~sP0(X0,X1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(k2_relat_1(sK5(X0,X1)),X0) & k1_relat_1(sK5(X0,X1)) = X1 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0,X1] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) | ~sP0(X0,X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f28])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(sK5(X0,k1_xboole_0)) | r1_tarski(sK5(X0,k1_xboole_0),k1_xboole_0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f107,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    inference(flattening,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(sK5(X0,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5(X0,k1_xboole_0)))) | ~v1_relat_1(sK5(X0,k1_xboole_0))) )),
% 0.21/0.51    inference(superposition,[],[f54,f105])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK5(X0,k1_xboole_0))) )),
% 0.21/0.51    inference(resolution,[],[f67,f85])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~sP0(X0,X1) | k1_relat_1(sK5(X0,X1)) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 0.21/0.51    inference(resolution,[],[f72,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.51    inference(resolution,[],[f86,f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP1(X0,k1_xboole_0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f77,f53])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(definition_folding,[],[f25,f30])).
% 0.21/0.51  % (28717)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X2,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~sP1(k1_xboole_0,X1,X2) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1) | v1_funct_2(X1,k1_xboole_0,X2)) )),
% 0.21/0.51    inference(equality_resolution,[],[f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 != X0 | ~sP1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP1(X0,X1,X2))),
% 0.21/0.51    inference(rectify,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X2,X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f30])).
% 0.21/0.51  fof(f279,plain,(
% 0.21/0.51    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    inference(forward_demodulation,[],[f271,f118])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.51    inference(backward_demodulation,[],[f234,f268])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    k1_xboole_0 = sK3),
% 0.21/0.51    inference(forward_demodulation,[],[f267,f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    sK3 = k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f266,f52])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)),
% 0.21/0.51    inference(forward_demodulation,[],[f265,f83])).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0),sK3) | sK3 = k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f263,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    v1_relat_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3)) & r1_tarski(k2_relat_1(sK3),sK2) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3)) & r1_tarski(k2_relat_1(sK3),sK2) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f13])).
% 0.21/0.51  fof(f13,conjecture,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0),sK3) | sK3 = k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0) | ~v1_relat_1(sK3)),
% 0.21/0.51    inference(superposition,[],[f101,f239])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f238,f52])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,k2_relat_1(sK3)) | k1_xboole_0 = k2_relat_1(sK3)),
% 0.21/0.51    inference(forward_demodulation,[],[f224,f222])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    k1_xboole_0 = sK2),
% 0.21/0.51    inference(subsumption_resolution,[],[f221,f207])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,k1_relat_1(sK3),sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f91,f206])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 0.21/0.51    inference(resolution,[],[f202,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))) )),
% 0.21/0.51    inference(resolution,[],[f200,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    ( ! [X6,X7] : (~r1_tarski(k1_relat_1(sK3),X7) | ~r1_tarski(k2_relat_1(sK3),X6) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X6)))) )),
% 0.21/0.51    inference(resolution,[],[f71,f48])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f51,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | v1_funct_2(sK3,k1_relat_1(sK3),sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f218,f208])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),sK2,sK3)),
% 0.21/0.52    inference(resolution,[],[f206,f72])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    k1_relat_1(sK3) != k1_relset_1(k1_relat_1(sK3),sK2,sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,k1_relat_1(sK3),sK2)),
% 0.21/0.52    inference(resolution,[],[f75,f209])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    sP1(k1_relat_1(sK3),sK3,sK2)),
% 0.21/0.52    inference(resolution,[],[f206,f77])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 = X2 | v1_funct_2(X1,X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(sK3) | ~r1_tarski(sK2,k2_relat_1(sK3))),
% 0.21/0.52    inference(backward_demodulation,[],[f100,f222])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ~r1_tarski(sK2,k2_relat_1(sK3)) | sK2 = k2_relat_1(sK3)),
% 0.21/0.52    inference(resolution,[],[f58,f50])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)),X2) | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) = X2 | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(resolution,[],[f58,f54])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    ~v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0)),
% 0.21/0.52    inference(backward_demodulation,[],[f207,f222])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (28696)------------------------------
% 0.21/0.52  % (28696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28696)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (28696)Memory used [KB]: 6396
% 0.21/0.52  % (28696)Time elapsed: 0.095 s
% 0.21/0.52  % (28696)------------------------------
% 0.21/0.52  % (28696)------------------------------
% 0.21/0.52  % (28688)Success in time 0.156 s
%------------------------------------------------------------------------------
