%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 (4205 expanded)
%              Number of leaves         :   16 (1044 expanded)
%              Depth                    :   24
%              Number of atoms          :  351 (25570 expanded)
%              Number of equality atoms :   95 (4055 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f398,plain,(
    $false ),
    inference(subsumption_resolution,[],[f397,f391])).

fof(f391,plain,(
    ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f390,f309])).

fof(f309,plain,(
    k1_xboole_0 = sK2 ),
    inference(unit_resulting_resolution,[],[f49,f305,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f305,plain,(
    v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f49,f283,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f283,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f253,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
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

fof(f253,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f45,f251])).

fof(f251,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f48,f109,f205,f246])).

fof(f246,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f142,f178])).

fof(f178,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f104,f91])).

fof(f91,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f45,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f104,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f95,f44])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

% (16523)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (16513)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (16518)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (16525)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (16520)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f38,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f95,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f45,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f142,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f141,f103])).

fof(f103,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f102,f93])).

fof(f93,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f45,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f102,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f89,f101])).

fof(f101,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f92,f47])).

fof(f47,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f45,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f89,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f87,f43])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f46,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f46,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f141,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f140,f111])).

fof(f111,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f43,f93,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f140,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    inference(subsumption_resolution,[],[f130,f109])).

fof(f130,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    inference(resolution,[],[f108,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f108,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f43,f93,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f205,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f139,f178])).

fof(f139,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f138,f103])).

fof(f138,plain,(
    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f137,f111])).

fof(f137,plain,(
    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f129,f109])).

fof(f129,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) ),
    inference(resolution,[],[f108,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f109,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f43,f93,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f390,plain,(
    ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f359,f385])).

fof(f385,plain,(
    ! [X0] : v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f384,f309])).

fof(f384,plain,(
    ! [X0] : v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f383,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f383,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f352,f50])).

fof(f50,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f352,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0) ) ),
    inference(backward_demodulation,[],[f264,f309])).

fof(f264,plain,(
    ! [X0] :
      ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0)
      | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(backward_demodulation,[],[f133,f251])).

fof(f133,plain,(
    ! [X0] :
      ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
      | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(forward_demodulation,[],[f132,f103])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0) ) ),
    inference(forward_demodulation,[],[f131,f111])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f127,f109])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | ~ v1_funct_1(k2_funct_1(sK2))
      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0) ) ),
    inference(resolution,[],[f108,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f359,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f286,f309])).

fof(f286,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f285,f251])).

fof(f285,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f284,f81])).

fof(f81,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f284,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f255,f109])).

fof(f255,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f48,f251])).

fof(f397,plain,(
    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f396,f309])).

fof(f396,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f395,f52])).

fof(f395,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f363,f50])).

fof(f363,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X1)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(backward_demodulation,[],[f291,f309])).

fof(f291,plain,(
    ! [X1] :
      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(forward_demodulation,[],[f265,f81])).

fof(f265,plain,(
    ! [X1] :
      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(backward_demodulation,[],[f136,f251])).

fof(f136,plain,(
    ! [X1] :
      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(forward_demodulation,[],[f135,f103])).

fof(f135,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1))) ) ),
    inference(forward_demodulation,[],[f134,f111])).

fof(f134,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1))) ) ),
    inference(subsumption_resolution,[],[f128,f109])).

fof(f128,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1)
      | ~ v1_funct_1(k2_funct_1(sK2))
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1))) ) ),
    inference(resolution,[],[f108,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (16519)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (16516)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (16527)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (16517)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (16524)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (16526)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (16524)Refutation not found, incomplete strategy% (16524)------------------------------
% 0.21/0.49  % (16524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (16524)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (16524)Memory used [KB]: 1663
% 0.21/0.49  % (16524)Time elapsed: 0.068 s
% 0.21/0.49  % (16524)------------------------------
% 0.21/0.49  % (16524)------------------------------
% 0.21/0.49  % (16526)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f398,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f397,f391])).
% 0.21/0.49  fof(f391,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    inference(forward_demodulation,[],[f390,f309])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    k1_xboole_0 = sK2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f49,f305,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    v1_xboole_0(sK2)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f49,f283,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    inference(forward_demodulation,[],[f253,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(flattening,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.49    inference(backward_demodulation,[],[f45,f251])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    k1_xboole_0 = sK1),
% 0.21/0.49    inference(global_subsumption,[],[f48,f109,f205,f246])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK1),
% 0.21/0.49    inference(superposition,[],[f142,f178])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.21/0.49    inference(superposition,[],[f104,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f45,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.21/0.49    inference(subsumption_resolution,[],[f95,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  % (16523)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (16513)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (16518)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (16525)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (16520)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f17])).
% 0.21/0.51  fof(f17,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    inference(resolution,[],[f45,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.21/0.51    inference(forward_demodulation,[],[f141,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f102,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    v1_relat_1(sK2)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f45,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(backward_demodulation,[],[f89,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    sK1 = k2_relat_1(sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f92,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f45,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f87,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f46,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    v2_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))),
% 0.21/0.51    inference(forward_demodulation,[],[f140,f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f46,f43,f93,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f130,f109])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ~v1_funct_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 0.21/0.51    inference(resolution,[],[f108,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f43,f93,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(superposition,[],[f139,f178])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.21/0.51    inference(forward_demodulation,[],[f138,f103])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))),
% 0.21/0.51    inference(forward_demodulation,[],[f137,f111])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f129,f109])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    ~v1_funct_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))),
% 0.21/0.51    inference(resolution,[],[f108,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f43,f93,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f390,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f359,f385])).
% 0.21/0.51  fof(f385,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f384,f309])).
% 0.21/0.51  fof(f384,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f383,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f383,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f352,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.51  fof(f352,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(k1_xboole_0),X0) | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0)) )),
% 0.21/0.51    inference(backward_demodulation,[],[f264,f309])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0) | ~r1_tarski(k1_relat_1(sK2),X0)) )),
% 0.21/0.51    inference(backward_demodulation,[],[f133,f251])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(k1_relat_1(sK2),X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f132,f103])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f131,f111])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f109])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | ~v1_funct_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0)) )),
% 0.21/0.51    inference(resolution,[],[f108,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.51  fof(f359,plain,(
% 0.21/0.51    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    inference(backward_demodulation,[],[f286,f309])).
% 0.21/0.51  fof(f286,plain,(
% 0.21/0.51    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    inference(forward_demodulation,[],[f285,f251])).
% 0.21/0.51  fof(f285,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f284,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f255,f109])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(backward_demodulation,[],[f48,f251])).
% 0.21/0.51  fof(f397,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    inference(forward_demodulation,[],[f396,f309])).
% 0.21/0.51  fof(f396,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f395,f52])).
% 0.21/0.51  fof(f395,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f363,f50])).
% 0.21/0.51  fof(f363,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_tarski(k1_relat_1(k1_xboole_0),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.51    inference(backward_demodulation,[],[f291,f309])).
% 0.21/0.51  fof(f291,plain,(
% 0.21/0.51    ( ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(sK2),X1)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f265,f81])).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    ( ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_tarski(k1_relat_1(sK2),X1)) )),
% 0.21/0.51    inference(backward_demodulation,[],[f136,f251])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(k1_relat_1(sK2),X1)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f135,f103])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1)))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f134,f111])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f128,f109])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1) | ~v1_funct_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1)))) )),
% 0.21/0.51    inference(resolution,[],[f108,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (16526)------------------------------
% 0.21/0.51  % (16526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16526)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (16526)Memory used [KB]: 6268
% 0.21/0.51  % (16526)Time elapsed: 0.071 s
% 0.21/0.51  % (16526)------------------------------
% 0.21/0.51  % (16526)------------------------------
% 0.21/0.51  % (16510)Success in time 0.149 s
%------------------------------------------------------------------------------
