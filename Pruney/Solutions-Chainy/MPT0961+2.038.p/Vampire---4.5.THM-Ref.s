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
% DateTime   : Thu Dec  3 13:00:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 710 expanded)
%              Number of leaves         :   13 ( 166 expanded)
%              Depth                    :   18
%              Number of atoms          :  207 (2226 expanded)
%              Number of equality atoms :   57 ( 384 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f127,f208,f226,f291,f305])).

fof(f305,plain,
    ( ~ spl1_1
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f231,f290])).

fof(f290,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl1_5
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f231,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(backward_demodulation,[],[f136,f203])).

fof(f203,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f136,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl1_1 ),
    inference(backward_demodulation,[],[f86,f110])).

fof(f110,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl1_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f86,plain,(
    ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) ),
    inference(global_subsumption,[],[f71,f85])).

fof(f85,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f84,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f84,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f83,f61])).

fof(f61,plain,(
    k1_xboole_0 = k2_relat_1(sK0) ),
    inference(global_subsumption,[],[f57,f55])).

fof(f55,plain,(
    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) ),
    inference(resolution,[],[f50,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f50,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(resolution,[],[f49,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f49,plain,(
    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f19,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f57,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(global_subsumption,[],[f48,f50,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f48,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(global_subsumption,[],[f20,f18])).

fof(f18,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(forward_demodulation,[],[f48,f61])).

fof(f71,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f68,f26])).

fof(f68,plain,(
    r1_tarski(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f65,f41])).

fof(f65,plain,(
    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f49,f61])).

fof(f291,plain,
    ( spl1_5
    | ~ spl1_4
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f282,f201,f108,f205,f288])).

fof(f205,plain,
    ( spl1_4
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f282,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f278,f41])).

fof(f278,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(trivial_inequality_removal,[],[f274])).

fof(f274,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(superposition,[],[f44,f266])).

fof(f266,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f265,f203])).

fof(f265,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl1_1 ),
    inference(forward_demodulation,[],[f63,f110])).

fof(f63,plain,(
    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f55,f61])).

fof(f44,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f226,plain,
    ( ~ spl1_1
    | spl1_4 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl1_1
    | spl1_4 ),
    inference(subsumption_resolution,[],[f134,f207])).

fof(f207,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f205])).

fof(f134,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl1_1 ),
    inference(backward_demodulation,[],[f67,f110])).

fof(f67,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f64,f41])).

fof(f64,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f50,f61])).

% (5703)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% (5712)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f208,plain,
    ( spl1_3
    | ~ spl1_4
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f165,f108,f205,f201])).

fof(f165,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_1 ),
    inference(forward_demodulation,[],[f157,f41])).

fof(f157,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_1 ),
    inference(resolution,[],[f136,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f127,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl1_2 ),
    inference(resolution,[],[f114,f21])).

fof(f21,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f114,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl1_2
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f115,plain,
    ( spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f72,f112,f108])).

fof(f72,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f68,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:26:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (5705)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.50  % (5700)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (5713)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (5711)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (5704)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (5713)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f309,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f115,f127,f208,f226,f291,f305])).
% 0.22/0.53  fof(f305,plain,(
% 0.22/0.53    ~spl1_1 | ~spl1_3 | ~spl1_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f295])).
% 0.22/0.53  fof(f295,plain,(
% 0.22/0.53    $false | (~spl1_1 | ~spl1_3 | ~spl1_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f231,f290])).
% 0.22/0.53  fof(f290,plain,(
% 0.22/0.53    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl1_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f288])).
% 0.22/0.53  fof(f288,plain,(
% 0.22/0.53    spl1_5 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl1_1 | ~spl1_3)),
% 0.22/0.53    inference(backward_demodulation,[],[f136,f203])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f201])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~spl1_1),
% 0.22/0.53    inference(backward_demodulation,[],[f86,f110])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    k1_xboole_0 = sK0 | ~spl1_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    spl1_1 <=> k1_xboole_0 = sK0),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)),
% 0.22/0.53    inference(global_subsumption,[],[f71,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ~m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)),
% 0.22/0.53    inference(forward_demodulation,[],[f84,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)),
% 0.22/0.53    inference(forward_demodulation,[],[f83,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(sK0)),
% 0.22/0.53    inference(global_subsumption,[],[f57,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)),
% 0.22/0.53    inference(resolution,[],[f50,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.22/0.53    inference(resolution,[],[f49,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.22/0.53    inference(resolution,[],[f19,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    v1_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | k1_xboole_0 = k2_relat_1(sK0)),
% 0.22/0.53    inference(global_subsumption,[],[f48,f50,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(sK0) | k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.53    inference(resolution,[],[f50,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.22/0.53    inference(global_subsumption,[],[f20,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ~v1_funct_1(sK0) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    v1_funct_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.22/0.53    inference(forward_demodulation,[],[f48,f61])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.53    inference(resolution,[],[f68,f26])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    r1_tarski(sK0,k1_xboole_0)),
% 0.22/0.53    inference(forward_demodulation,[],[f65,f41])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))),
% 0.22/0.53    inference(backward_demodulation,[],[f49,f61])).
% 0.22/0.53  fof(f291,plain,(
% 0.22/0.53    spl1_5 | ~spl1_4 | ~spl1_1 | ~spl1_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f282,f201,f108,f205,f288])).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    spl1_4 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.53  fof(f282,plain,(
% 0.22/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl1_1 | ~spl1_3)),
% 0.22/0.53    inference(forward_demodulation,[],[f278,f41])).
% 0.22/0.53  fof(f278,plain,(
% 0.22/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl1_1 | ~spl1_3)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f274])).
% 0.22/0.53  fof(f274,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl1_1 | ~spl1_3)),
% 0.22/0.53    inference(superposition,[],[f44,f266])).
% 0.22/0.53  fof(f266,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl1_1 | ~spl1_3)),
% 0.22/0.53    inference(forward_demodulation,[],[f265,f203])).
% 0.22/0.53  fof(f265,plain,(
% 0.22/0.53    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~spl1_1),
% 0.22/0.53    inference(forward_demodulation,[],[f63,f110])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0)),
% 0.22/0.53    inference(backward_demodulation,[],[f55,f61])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    ~spl1_1 | spl1_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f218])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    $false | (~spl1_1 | spl1_4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f134,f207])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl1_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f205])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl1_1),
% 0.22/0.53    inference(backward_demodulation,[],[f67,f110])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.53    inference(forward_demodulation,[],[f64,f41])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))),
% 0.22/0.53    inference(backward_demodulation,[],[f50,f61])).
% 0.22/0.53  % (5703)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (5712)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.54  fof(f208,plain,(
% 0.22/0.54    spl1_3 | ~spl1_4 | ~spl1_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f165,f108,f205,f201])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_1),
% 0.22/0.54    inference(forward_demodulation,[],[f157,f41])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_1),
% 0.22/0.54    inference(resolution,[],[f136,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    spl1_2),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f119])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    $false | spl1_2),
% 0.22/0.54    inference(resolution,[],[f114,f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ~r1_tarski(k1_xboole_0,sK0) | spl1_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f112])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    spl1_2 <=> r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    spl1_1 | ~spl1_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f72,f112,f108])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ~r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(resolution,[],[f68,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (5713)------------------------------
% 0.22/0.54  % (5713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5713)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (5713)Memory used [KB]: 10746
% 0.22/0.54  % (5713)Time elapsed: 0.123 s
% 0.22/0.54  % (5713)------------------------------
% 0.22/0.54  % (5713)------------------------------
% 0.22/0.54  % (5692)Success in time 0.177 s
%------------------------------------------------------------------------------
