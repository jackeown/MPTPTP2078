%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 (3929 expanded)
%              Number of leaves         :   13 ( 940 expanded)
%              Depth                    :   31
%              Number of atoms          :  347 (21955 expanded)
%              Number of equality atoms :  107 (4835 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(global_subsumption,[],[f237,f307])).

fof(f307,plain,(
    ~ v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f217,f294])).

fof(f294,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f227,f292])).

fof(f292,plain,(
    k1_xboole_0 = k1_relat_1(sK4) ),
    inference(resolution,[],[f276,f237])).

fof(f276,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
      | k1_xboole_0 = k1_relat_1(sK4) ) ),
    inference(forward_demodulation,[],[f274,f258])).

fof(f258,plain,(
    ! [X0] : k1_relat_1(sK4) = k1_relset_1(k1_xboole_0,X0,sK4) ),
    inference(subsumption_resolution,[],[f221,f253])).

fof(f253,plain,(
    ! [X0] : v5_relat_1(sK4,X0) ),
    inference(global_subsumption,[],[f71,f95,f207])).

fof(f207,plain,(
    v5_relat_1(sK4,k1_xboole_0) ),
    inference(backward_demodulation,[],[f83,f200])).

fof(f200,plain,(
    k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f177,f77])).

fof(f77,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f46,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f177,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f38,f176])).

fof(f176,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f175])).

fof(f175,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f172,f161])).

fof(f161,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f36,f160])).

% (21431)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% (21434)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f160,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f156,f118])).

fof(f118,plain,(
    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f48,f37])).

fof(f37,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f27])).

fof(f27,plain,
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
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
        | ~ v1_funct_2(sK4,sK1,sK3)
        | ~ v1_funct_1(sK4) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f11])).

% (21435)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f156,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f50,f117])).

fof(f117,plain,(
    sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f54,f37])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f20,f25])).

fof(f25,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f36,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f172,plain,
    ( sK1 != k1_relat_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(global_subsumption,[],[f92,f170])).

fof(f170,plain,
    ( k1_xboole_0 = sK3
    | sK1 != k1_relat_1(sK4)
    | ~ v5_relat_1(sK4,sK3) ),
    inference(resolution,[],[f168,f145])).

fof(f145,plain,(
    ! [X0] :
      ( sP0(sK1,sK4,X0)
      | ~ v5_relat_1(sK4,X0) ) ),
    inference(resolution,[],[f141,f112])).

fof(f112,plain,(
    sP5(sK4,sK1) ),
    inference(resolution,[],[f66,f37])).

fof(f66,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | sP5(X3,X2) ) ),
    inference(cnf_transformation,[],[f66_D])).

fof(f66_D,plain,(
    ! [X2,X3] :
      ( ! [X0] : ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    <=> ~ sP5(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f141,plain,(
    ! [X2,X3] :
      ( ~ sP5(sK4,X2)
      | ~ v5_relat_1(sK4,X3)
      | sP0(X2,sK4,X3) ) ),
    inference(resolution,[],[f119,f54])).

fof(f119,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP5(sK4,X0)
      | ~ v5_relat_1(sK4,X1) ) ),
    inference(resolution,[],[f67,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK4),X0)
      | ~ v5_relat_1(sK4,X0) ) ),
    inference(resolution,[],[f42,f69])).

fof(f69,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f47,f37])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f67,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ sP5(X3,X2) ) ),
    inference(general_splitting,[],[f58,f66_D])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f168,plain,
    ( ~ sP0(sK1,sK4,sK3)
    | k1_xboole_0 = sK3
    | sK1 != k1_relat_1(sK4) ),
    inference(global_subsumption,[],[f129,f166])).

fof(f166,plain,
    ( sK1 != k1_relat_1(sK4)
    | v1_funct_2(sK4,sK1,sK3)
    | k1_xboole_0 = sK3
    | ~ sP0(sK1,sK4,sK3) ),
    inference(superposition,[],[f52,f130])).

fof(f130,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,sK3,sK4) ),
    inference(resolution,[],[f124,f112])).

fof(f124,plain,(
    ! [X0] :
      ( ~ sP5(sK4,X0)
      | k1_relat_1(sK4) = k1_relset_1(X0,sK3,sK4) ) ),
    inference(resolution,[],[f120,f48])).

fof(f120,plain,(
    ! [X2] :
      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3)))
      | ~ sP5(sK4,X2) ) ),
    inference(resolution,[],[f67,f100])).

fof(f100,plain,(
    r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(resolution,[],[f99,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f99,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(sK4))
      | r1_tarski(X2,sK3) ) ),
    inference(global_subsumption,[],[f83,f98])).

fof(f98,plain,(
    ! [X2] :
      ( r1_tarski(X2,sK3)
      | ~ r1_tarski(X2,k2_relat_1(sK4))
      | ~ v5_relat_1(sK4,sK2) ) ),
    inference(resolution,[],[f88,f70])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK2)
      | r1_tarski(X1,sK3)
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f87,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f87,plain,(
    ! [X6] :
      ( r1_tarski(X6,sK3)
      | ~ r1_tarski(X6,sK2) ) ),
    inference(resolution,[],[f57,f38])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f129,plain,(
    ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(global_subsumption,[],[f112,f123])).

fof(f123,plain,
    ( ~ sP5(sK4,sK1)
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(resolution,[],[f120,f68])).

fof(f68,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(subsumption_resolution,[],[f40,f35])).

fof(f35,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    v5_relat_1(sK4,sK3) ),
    inference(global_subsumption,[],[f83,f91])).

fof(f91,plain,
    ( v5_relat_1(sK4,sK3)
    | ~ v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f90,f70])).

fof(f90,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK2)
    | v5_relat_1(sK4,sK3) ),
    inference(resolution,[],[f87,f71])).

fof(f38,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f49,f37])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f95,plain,(
    ! [X2] :
      ( ~ v5_relat_1(sK4,k1_xboole_0)
      | r1_tarski(k2_relat_1(sK4),X2) ) ),
    inference(resolution,[],[f85,f70])).

fof(f85,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f57,f41])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK4),X0)
      | v5_relat_1(sK4,X0) ) ),
    inference(resolution,[],[f43,f69])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f221,plain,(
    ! [X0] :
      ( k1_relat_1(sK4) = k1_relset_1(k1_xboole_0,X0,sK4)
      | ~ v5_relat_1(sK4,X0) ) ),
    inference(backward_demodulation,[],[f147,f201])).

fof(f201,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f39,f200])).

fof(f39,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f147,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK4,X0)
      | k1_relat_1(sK4) = k1_relset_1(sK1,X0,sK4) ) ),
    inference(resolution,[],[f140,f112])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ sP5(sK4,X0)
      | ~ v5_relat_1(sK4,X1)
      | k1_relat_1(sK4) = k1_relset_1(X0,X1,sK4) ) ),
    inference(resolution,[],[f119,f48])).

fof(f274,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK4) ) ),
    inference(resolution,[],[f257,f62])).

fof(f62,plain,(
    ! [X2,X1] :
      ( ~ sP0(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X1,k1_xboole_0,X2)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f257,plain,(
    ! [X0] : sP0(k1_xboole_0,sK4,X0) ),
    inference(subsumption_resolution,[],[f220,f253])).

fof(f220,plain,(
    ! [X0] :
      ( sP0(k1_xboole_0,sK4,X0)
      | ~ v5_relat_1(sK4,X0) ) ),
    inference(backward_demodulation,[],[f145,f201])).

fof(f227,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(backward_demodulation,[],[f172,f201])).

fof(f217,plain,(
    ~ v1_funct_2(sK4,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f129,f201])).

fof(f237,plain,(
    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f202,f201])).

fof(f202,plain,(
    v1_funct_2(sK4,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f36,f200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (21441)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (21433)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (21433)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f309,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(global_subsumption,[],[f237,f307])).
% 0.20/0.50  fof(f307,plain,(
% 0.20/0.50    ~v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    inference(backward_demodulation,[],[f217,f294])).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    k1_xboole_0 = sK3),
% 0.20/0.50    inference(subsumption_resolution,[],[f227,f292])).
% 0.20/0.50  fof(f292,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK4)),
% 0.20/0.50    inference(resolution,[],[f276,f237])).
% 0.20/0.50  fof(f276,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_2(sK4,k1_xboole_0,X0) | k1_xboole_0 = k1_relat_1(sK4)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f274,f258])).
% 0.20/0.50  fof(f258,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(sK4) = k1_relset_1(k1_xboole_0,X0,sK4)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f221,f253])).
% 0.20/0.50  fof(f253,plain,(
% 0.20/0.50    ( ! [X0] : (v5_relat_1(sK4,X0)) )),
% 0.20/0.50    inference(global_subsumption,[],[f71,f95,f207])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    v5_relat_1(sK4,k1_xboole_0)),
% 0.20/0.50    inference(backward_demodulation,[],[f83,f200])).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    k1_xboole_0 = sK2),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f196])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.20/0.50    inference(resolution,[],[f177,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.20/0.50    inference(resolution,[],[f46,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2),
% 0.20/0.51    inference(superposition,[],[f38,f176])).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f175])).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    sK1 != sK1 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 0.20/0.51    inference(superposition,[],[f172,f161])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    sK1 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 0.20/0.51    inference(global_subsumption,[],[f36,f160])).
% 0.20/0.51  % (21431)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (21434)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    sK1 = k1_relat_1(sK4) | ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2),
% 0.20/0.52    inference(forward_demodulation,[],[f156,f118])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)),
% 0.20/0.52    inference(resolution,[],[f48,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  % (21435)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  fof(f11,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.52    inference(negated_conjecture,[],[f10])).
% 0.20/0.52  fof(f10,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 0.20/0.52    inference(resolution,[],[f50,f117])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    sP0(sK1,sK4,sK2)),
% 0.20/0.52    inference(resolution,[],[f54,f37])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(definition_folding,[],[f20,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.20/0.52    inference(rectify,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f25])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    v1_funct_2(sK4,sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    sK1 != k1_relat_1(sK4) | k1_xboole_0 = sK3),
% 0.20/0.52    inference(global_subsumption,[],[f92,f170])).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    k1_xboole_0 = sK3 | sK1 != k1_relat_1(sK4) | ~v5_relat_1(sK4,sK3)),
% 0.20/0.52    inference(resolution,[],[f168,f145])).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    ( ! [X0] : (sP0(sK1,sK4,X0) | ~v5_relat_1(sK4,X0)) )),
% 0.20/0.52    inference(resolution,[],[f141,f112])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    sP5(sK4,sK1)),
% 0.20/0.52    inference(resolution,[],[f66,f37])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | sP5(X3,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f66_D])).
% 0.20/0.52  fof(f66_D,plain,(
% 0.20/0.52    ( ! [X2,X3] : (( ! [X0] : ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) <=> ~sP5(X3,X2)) )),
% 0.20/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~sP5(sK4,X2) | ~v5_relat_1(sK4,X3) | sP0(X2,sK4,X3)) )),
% 0.20/0.52    inference(resolution,[],[f119,f54])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP5(sK4,X0) | ~v5_relat_1(sK4,X1)) )),
% 0.20/0.52    inference(resolution,[],[f67,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(sK4),X0) | ~v5_relat_1(sK4,X0)) )),
% 0.20/0.52    inference(resolution,[],[f42,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    v1_relat_1(sK4)),
% 0.20/0.52    inference(resolution,[],[f47,f37])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X2,X3,X1] : (~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~sP5(X3,X2)) )),
% 0.20/0.52    inference(general_splitting,[],[f58,f66_D])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.52    inference(flattening,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    ~sP0(sK1,sK4,sK3) | k1_xboole_0 = sK3 | sK1 != k1_relat_1(sK4)),
% 0.20/0.52    inference(global_subsumption,[],[f129,f166])).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    sK1 != k1_relat_1(sK4) | v1_funct_2(sK4,sK1,sK3) | k1_xboole_0 = sK3 | ~sP0(sK1,sK4,sK3)),
% 0.20/0.52    inference(superposition,[],[f52,f130])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    k1_relat_1(sK4) = k1_relset_1(sK1,sK3,sK4)),
% 0.20/0.52    inference(resolution,[],[f124,f112])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    ( ! [X0] : (~sP5(sK4,X0) | k1_relat_1(sK4) = k1_relset_1(X0,sK3,sK4)) )),
% 0.20/0.52    inference(resolution,[],[f120,f48])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ( ! [X2] : (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) | ~sP5(sK4,X2)) )),
% 0.20/0.52    inference(resolution,[],[f67,f100])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    r1_tarski(k2_relat_1(sK4),sK3)),
% 0.20/0.52    inference(resolution,[],[f99,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(sK4)) | r1_tarski(X2,sK3)) )),
% 0.20/0.52    inference(global_subsumption,[],[f83,f98])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    ( ! [X2] : (r1_tarski(X2,sK3) | ~r1_tarski(X2,k2_relat_1(sK4)) | ~v5_relat_1(sK4,sK2)) )),
% 0.20/0.52    inference(resolution,[],[f88,f70])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,sK2) | r1_tarski(X1,sK3) | ~r1_tarski(X1,X0)) )),
% 0.20/0.52    inference(resolution,[],[f87,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ( ! [X6] : (r1_tarski(X6,sK3) | ~r1_tarski(X6,sK2)) )),
% 0.20/0.52    inference(resolution,[],[f57,f38])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) != X0 | v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    ~v1_funct_2(sK4,sK1,sK3)),
% 0.20/0.52    inference(global_subsumption,[],[f112,f123])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    ~sP5(sK4,sK1) | ~v1_funct_2(sK4,sK1,sK3)),
% 0.20/0.52    inference(resolution,[],[f120,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f40,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    v1_funct_1(sK4)),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    v5_relat_1(sK4,sK3)),
% 0.20/0.52    inference(global_subsumption,[],[f83,f91])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    v5_relat_1(sK4,sK3) | ~v5_relat_1(sK4,sK2)),
% 0.20/0.52    inference(resolution,[],[f90,f70])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    ~r1_tarski(k2_relat_1(sK4),sK2) | v5_relat_1(sK4,sK3)),
% 0.20/0.52    inference(resolution,[],[f87,f71])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    r1_tarski(sK2,sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    v5_relat_1(sK4,sK2)),
% 0.20/0.52    inference(resolution,[],[f49,f37])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.52    inference(pure_predicate_removal,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X2] : (~v5_relat_1(sK4,k1_xboole_0) | r1_tarski(k2_relat_1(sK4),X2)) )),
% 0.20/0.52    inference(resolution,[],[f85,f70])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r1_tarski(X2,k1_xboole_0) | r1_tarski(X2,X3)) )),
% 0.20/0.52    inference(resolution,[],[f57,f41])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(sK4),X0) | v5_relat_1(sK4,X0)) )),
% 0.20/0.52    inference(resolution,[],[f43,f69])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f221,plain,(
% 0.20/0.52    ( ! [X0] : (k1_relat_1(sK4) = k1_relset_1(k1_xboole_0,X0,sK4) | ~v5_relat_1(sK4,X0)) )),
% 0.20/0.52    inference(backward_demodulation,[],[f147,f201])).
% 0.20/0.52  fof(f201,plain,(
% 0.20/0.52    k1_xboole_0 = sK1),
% 0.20/0.52    inference(subsumption_resolution,[],[f39,f200])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    ( ! [X0] : (~v5_relat_1(sK4,X0) | k1_relat_1(sK4) = k1_relset_1(sK1,X0,sK4)) )),
% 0.20/0.52    inference(resolution,[],[f140,f112])).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~sP5(sK4,X0) | ~v5_relat_1(sK4,X1) | k1_relat_1(sK4) = k1_relset_1(X0,X1,sK4)) )),
% 0.20/0.52    inference(resolution,[],[f119,f48])).
% 0.20/0.52  fof(f274,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_2(sK4,k1_xboole_0,X0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK4)) )),
% 0.20/0.52    inference(resolution,[],[f257,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~sP0(k1_xboole_0,X1,X2) | ~v1_funct_2(X1,k1_xboole_0,X2) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f257,plain,(
% 0.20/0.52    ( ! [X0] : (sP0(k1_xboole_0,sK4,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f220,f253])).
% 0.20/0.52  fof(f220,plain,(
% 0.20/0.52    ( ! [X0] : (sP0(k1_xboole_0,sK4,X0) | ~v5_relat_1(sK4,X0)) )),
% 0.20/0.52    inference(backward_demodulation,[],[f145,f201])).
% 0.20/0.52  fof(f227,plain,(
% 0.20/0.52    k1_xboole_0 != k1_relat_1(sK4) | k1_xboole_0 = sK3),
% 0.20/0.52    inference(backward_demodulation,[],[f172,f201])).
% 0.20/0.52  fof(f217,plain,(
% 0.20/0.52    ~v1_funct_2(sK4,k1_xboole_0,sK3)),
% 0.20/0.52    inference(backward_demodulation,[],[f129,f201])).
% 0.20/0.52  fof(f237,plain,(
% 0.20/0.52    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)),
% 0.20/0.52    inference(forward_demodulation,[],[f202,f201])).
% 0.20/0.52  fof(f202,plain,(
% 0.20/0.52    v1_funct_2(sK4,sK1,k1_xboole_0)),
% 0.20/0.52    inference(backward_demodulation,[],[f36,f200])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (21433)------------------------------
% 0.20/0.52  % (21433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (21433)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (21433)Memory used [KB]: 6396
% 0.20/0.52  % (21433)Time elapsed: 0.075 s
% 0.20/0.52  % (21433)------------------------------
% 0.20/0.52  % (21433)------------------------------
% 0.20/0.52  % (21420)Success in time 0.158 s
%------------------------------------------------------------------------------
