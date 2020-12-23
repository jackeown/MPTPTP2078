%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:09 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 819 expanded)
%              Number of leaves         :   33 ( 269 expanded)
%              Depth                    :   15
%              Number of atoms          :  674 (2685 expanded)
%              Number of equality atoms :  116 ( 783 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (28273)Refutation not found, incomplete strategy% (28273)------------------------------
% (28273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28273)Termination reason: Refutation not found, incomplete strategy

% (28273)Memory used [KB]: 10874
% (28273)Time elapsed: 0.133 s
% (28273)------------------------------
% (28273)------------------------------
fof(f720,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f111,f124,f131,f140,f145,f149,f174,f179,f197,f203,f213,f235,f270,f303,f424,f434,f451,f467,f477,f478,f711])).

fof(f711,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f710])).

fof(f710,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_22 ),
    inference(global_subsumption,[],[f155,f279,f709])).

% (28281)Refutation not found, incomplete strategy% (28281)------------------------------
% (28281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28281)Termination reason: Refutation not found, incomplete strategy

% (28281)Memory used [KB]: 10618
% (28281)Time elapsed: 0.107 s
% (28281)------------------------------
% (28281)------------------------------
fof(f709,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f192,f278])).

fof(f278,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f276,f130])).

fof(f130,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl7_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f276,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_22 ),
    inference(superposition,[],[f265,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f265,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl7_22
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f192,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f191,f162])).

fof(f162,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f152,f160])).

fof(f160,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f158,f130])).

fof(f158,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_7 ),
    inference(superposition,[],[f144,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f144,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl7_7
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f152,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f118,f138])).

fof(f138,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl7_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f118,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f116,f105])).

fof(f105,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f116,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_2 ),
    inference(resolution,[],[f110,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f110,plain,
    ( v2_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f108])).

% (28298)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f108,plain,
    ( spl7_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f191,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f190,f151])).

fof(f151,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f119,f138])).

fof(f119,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f117,f105])).

fof(f117,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl7_2 ),
    inference(resolution,[],[f110,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f190,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f184,f135])).

fof(f135,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl7_5
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f184,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl7_10 ),
    inference(resolution,[],[f178,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f178,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl7_10
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f279,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f189,f278])).

fof(f189,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f188,f162])).

fof(f188,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f187,f151])).

% (28285)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f187,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f183,f135])).

fof(f183,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl7_10 ),
    inference(resolution,[],[f178,f54])).

% (28279)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f54,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f155,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f41,f154])).

fof(f154,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f113,f138])).

fof(f113,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl7_1 ),
    inference(resolution,[],[f105,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f41,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f478,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f477,plain,
    ( ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_23
    | spl7_33 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_23
    | spl7_33 ),
    inference(subsumption_resolution,[],[f475,f359])).

fof(f359,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f358,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f358,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f357,f49])).

fof(f49,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f357,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f356,f333])).

fof(f333,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_18
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f331,f332])).

fof(f332,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_18
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f316,f48])).

% (28275)Refutation not found, incomplete strategy% (28275)------------------------------
% (28275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28275)Termination reason: Refutation not found, incomplete strategy

% (28275)Memory used [KB]: 6396
% (28275)Time elapsed: 0.133 s
% (28275)------------------------------
% (28275)------------------------------
fof(f48,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f316,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_18
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f234,f304])).

fof(f304,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f157,f293])).

fof(f293,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f196,f269])).

fof(f269,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl7_23
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f196,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl7_11
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f157,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl7_6 ),
    inference(resolution,[],[f138,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f234,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl7_18
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f331,plain,
    ( k1_xboole_0 != k2_relat_1(k2_funct_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f311,f304])).

fof(f311,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k2_funct_1(sK2))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f165,f304])).

fof(f165,plain,
    ( k1_xboole_0 != k2_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f135,f53])).

fof(f356,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f322,f333])).

fof(f322,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(k1_xboole_0))),k2_relat_1(k2_funct_1(k2_funct_1(k1_xboole_0))))))
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f246,f304])).

fof(f246,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(sK2))),k2_relat_1(k2_funct_1(k2_funct_1(sK2))))))
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f242,f202])).

fof(f202,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl7_12
  <=> v1_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f242,plain,
    ( ~ v1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(sK2))),k2_relat_1(k2_funct_1(k2_funct_1(sK2))))))
    | ~ spl7_14 ),
    inference(resolution,[],[f212,f55])).

fof(f212,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl7_14
  <=> v1_funct_1(k2_funct_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f475,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl7_33 ),
    inference(forward_demodulation,[],[f474,f96])).

fof(f96,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f474,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl7_33 ),
    inference(subsumption_resolution,[],[f473,f48])).

fof(f473,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl7_33 ),
    inference(superposition,[],[f462,f83])).

fof(f462,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | spl7_33 ),
    inference(avatar_component_clause,[],[f460])).

fof(f460,plain,
    ( spl7_33
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f467,plain,
    ( ~ spl7_33
    | spl7_34
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_23
    | spl7_29 ),
    inference(avatar_split_clause,[],[f441,f431,f267,f232,f210,f200,f194,f137,f133,f464,f460])).

fof(f464,plain,
    ( spl7_34
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f431,plain,
    ( spl7_29
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f441,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_23
    | spl7_29 ),
    inference(subsumption_resolution,[],[f440,f359])).

fof(f440,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | spl7_29 ),
    inference(forward_demodulation,[],[f439,f96])).

fof(f439,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl7_29 ),
    inference(resolution,[],[f433,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f433,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl7_29 ),
    inference(avatar_component_clause,[],[f431])).

fof(f451,plain,
    ( spl7_31
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f304,f267,f194,f137,f448])).

fof(f448,plain,
    ( spl7_31
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f434,plain,
    ( ~ spl7_29
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9
    | ~ spl7_11
    | ~ spl7_18
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f381,f267,f232,f194,f171,f137,f133,f431])).

fof(f171,plain,
    ( spl7_9
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f381,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9
    | ~ spl7_11
    | ~ spl7_18
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f380,f333])).

fof(f380,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ spl7_6
    | spl7_9
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f379,f304])).

fof(f379,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl7_9
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f173,f269])).

fof(f173,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f424,plain,
    ( spl7_27
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f324,f267,f194,f137,f121,f421])).

fof(f421,plain,
    ( spl7_27
  <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f121,plain,
    ( spl7_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f324,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f287,f304])).

fof(f287,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f123,f269])).

fof(f123,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f303,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_10
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_10
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f301,f300])).

fof(f300,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl7_8
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f290,f96])).

fof(f290,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl7_8
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f169,f269])).

fof(f169,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl7_8
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f301,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f292,f96])).

fof(f292,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f192,f269])).

fof(f270,plain,
    ( spl7_22
    | spl7_23
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f126,f121,f267,f263])).

fof(f126,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f125,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f125,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(resolution,[],[f123,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f235,plain,
    ( spl7_18
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f151,f137,f108,f103,f232])).

fof(f213,plain,
    ( spl7_14
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f186,f176,f133,f210])).

fof(f186,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f182,f135])).

fof(f182,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl7_10 ),
    inference(resolution,[],[f178,f57])).

fof(f203,plain,
    ( spl7_12
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f185,f176,f133,f200])).

fof(f185,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f181,f135])).

fof(f181,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl7_10 ),
    inference(resolution,[],[f178,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f197,plain,
    ( spl7_11
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f160,f142,f128,f194])).

fof(f179,plain,
    ( spl7_10
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f154,f137,f103,f176])).

fof(f174,plain,
    ( ~ spl7_8
    | ~ spl7_9
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f155,f137,f103,f171,f167])).

fof(f149,plain,
    ( ~ spl7_4
    | spl7_6 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl7_4
    | spl7_6 ),
    inference(subsumption_resolution,[],[f130,f146])).

fof(f146,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_6 ),
    inference(resolution,[],[f139,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f139,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f137])).

fof(f145,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f46,f142])).

fof(f46,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f140,plain,
    ( spl7_5
    | ~ spl7_6
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f112,f103,f137,f133])).

fof(f112,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl7_1 ),
    inference(resolution,[],[f105,f56])).

fof(f131,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f44,f128])).

fof(f124,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f43,f121])).

fof(f43,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f111,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f45,f108])).

fof(f45,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f106,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f42,f103])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:45:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (28283)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (28291)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (28272)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.53  % (28271)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.53  % (28300)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.53  % (28294)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.53  % (28274)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.53  % (28286)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.53  % (28277)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.54  % (28289)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.54  % (28287)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.54  % (28299)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.54  % (28281)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.54  % (28280)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.54  % (28273)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.43/0.54  % (28291)Refutation found. Thanks to Tanya!
% 1.43/0.54  % SZS status Theorem for theBenchmark
% 1.43/0.54  % (28293)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.55  % (28275)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.43/0.55  % SZS output start Proof for theBenchmark
% 1.43/0.55  % (28273)Refutation not found, incomplete strategy% (28273)------------------------------
% 1.43/0.55  % (28273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (28273)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (28273)Memory used [KB]: 10874
% 1.43/0.55  % (28273)Time elapsed: 0.133 s
% 1.43/0.55  % (28273)------------------------------
% 1.43/0.55  % (28273)------------------------------
% 1.43/0.55  fof(f720,plain,(
% 1.43/0.55    $false),
% 1.43/0.55    inference(avatar_sat_refutation,[],[f106,f111,f124,f131,f140,f145,f149,f174,f179,f197,f203,f213,f235,f270,f303,f424,f434,f451,f467,f477,f478,f711])).
% 1.43/0.55  fof(f711,plain,(
% 1.43/0.55    ~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_10 | ~spl7_22),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f710])).
% 1.43/0.55  fof(f710,plain,(
% 1.43/0.55    $false | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_10 | ~spl7_22)),
% 1.43/0.55    inference(global_subsumption,[],[f155,f279,f709])).
% 1.43/0.55  % (28281)Refutation not found, incomplete strategy% (28281)------------------------------
% 1.43/0.55  % (28281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (28281)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (28281)Memory used [KB]: 10618
% 1.43/0.55  % (28281)Time elapsed: 0.107 s
% 1.43/0.55  % (28281)------------------------------
% 1.43/0.55  % (28281)------------------------------
% 1.43/0.55  fof(f709,plain,(
% 1.43/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_10 | ~spl7_22)),
% 1.43/0.55    inference(forward_demodulation,[],[f192,f278])).
% 1.43/0.55  fof(f278,plain,(
% 1.43/0.55    sK0 = k1_relat_1(sK2) | (~spl7_4 | ~spl7_22)),
% 1.43/0.55    inference(subsumption_resolution,[],[f276,f130])).
% 1.43/0.55  fof(f130,plain,(
% 1.43/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_4),
% 1.43/0.55    inference(avatar_component_clause,[],[f128])).
% 1.43/0.55  fof(f128,plain,(
% 1.43/0.55    spl7_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.43/0.55  fof(f276,plain,(
% 1.43/0.55    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_22),
% 1.43/0.55    inference(superposition,[],[f265,f83])).
% 1.43/0.55  fof(f83,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f37])).
% 1.43/0.55  fof(f37,plain,(
% 1.43/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.55    inference(ennf_transformation,[],[f15])).
% 1.43/0.55  fof(f15,axiom,(
% 1.43/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.43/0.55  fof(f265,plain,(
% 1.43/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_22),
% 1.43/0.55    inference(avatar_component_clause,[],[f263])).
% 1.43/0.55  fof(f263,plain,(
% 1.43/0.55    spl7_22 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.43/0.55  fof(f192,plain,(
% 1.43/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_10)),
% 1.43/0.55    inference(forward_demodulation,[],[f191,f162])).
% 1.43/0.55  fof(f162,plain,(
% 1.43/0.55    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_6 | ~spl7_7)),
% 1.43/0.55    inference(backward_demodulation,[],[f152,f160])).
% 1.43/0.55  fof(f160,plain,(
% 1.43/0.55    sK1 = k2_relat_1(sK2) | (~spl7_4 | ~spl7_7)),
% 1.43/0.55    inference(subsumption_resolution,[],[f158,f130])).
% 1.43/0.55  fof(f158,plain,(
% 1.43/0.55    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_7),
% 1.43/0.55    inference(superposition,[],[f144,f84])).
% 1.43/0.55  fof(f84,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f38])).
% 1.43/0.55  fof(f38,plain,(
% 1.43/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.55    inference(ennf_transformation,[],[f16])).
% 1.43/0.55  fof(f16,axiom,(
% 1.43/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.43/0.55  fof(f144,plain,(
% 1.43/0.55    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl7_7),
% 1.43/0.55    inference(avatar_component_clause,[],[f142])).
% 1.43/0.55  fof(f142,plain,(
% 1.43/0.55    spl7_7 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.43/0.55  fof(f152,plain,(
% 1.43/0.55    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_6)),
% 1.43/0.55    inference(subsumption_resolution,[],[f118,f138])).
% 1.43/0.55  fof(f138,plain,(
% 1.43/0.55    v1_relat_1(sK2) | ~spl7_6),
% 1.43/0.55    inference(avatar_component_clause,[],[f137])).
% 1.43/0.55  fof(f137,plain,(
% 1.43/0.55    spl7_6 <=> v1_relat_1(sK2)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.43/0.55  fof(f118,plain,(
% 1.43/0.55    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2)),
% 1.43/0.55    inference(subsumption_resolution,[],[f116,f105])).
% 1.43/0.55  fof(f105,plain,(
% 1.43/0.55    v1_funct_1(sK2) | ~spl7_1),
% 1.43/0.55    inference(avatar_component_clause,[],[f103])).
% 1.43/0.55  fof(f103,plain,(
% 1.43/0.55    spl7_1 <=> v1_funct_1(sK2)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.43/0.55  fof(f116,plain,(
% 1.43/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl7_2),
% 1.43/0.55    inference(resolution,[],[f110,f58])).
% 1.43/0.55  fof(f58,plain,(
% 1.43/0.55    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f33])).
% 1.43/0.55  fof(f33,plain,(
% 1.43/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.43/0.55    inference(flattening,[],[f32])).
% 1.43/0.55  fof(f32,plain,(
% 1.43/0.55    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.43/0.55    inference(ennf_transformation,[],[f13])).
% 1.43/0.55  fof(f13,axiom,(
% 1.43/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.43/0.55  fof(f110,plain,(
% 1.43/0.55    v2_funct_1(sK2) | ~spl7_2),
% 1.43/0.55    inference(avatar_component_clause,[],[f108])).
% 1.43/0.55  % (28298)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.55  fof(f108,plain,(
% 1.43/0.55    spl7_2 <=> v2_funct_1(sK2)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.43/0.55  fof(f191,plain,(
% 1.43/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl7_1 | ~spl7_2 | ~spl7_5 | ~spl7_6 | ~spl7_10)),
% 1.43/0.55    inference(forward_demodulation,[],[f190,f151])).
% 1.43/0.55  fof(f151,plain,(
% 1.43/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_6)),
% 1.43/0.55    inference(subsumption_resolution,[],[f119,f138])).
% 1.43/0.55  fof(f119,plain,(
% 1.43/0.55    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_2)),
% 1.43/0.55    inference(subsumption_resolution,[],[f117,f105])).
% 1.43/0.55  fof(f117,plain,(
% 1.43/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl7_2),
% 1.43/0.55    inference(resolution,[],[f110,f59])).
% 1.43/0.55  fof(f59,plain,(
% 1.43/0.55    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f33])).
% 1.43/0.55  fof(f190,plain,(
% 1.43/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | (~spl7_5 | ~spl7_10)),
% 1.43/0.55    inference(subsumption_resolution,[],[f184,f135])).
% 1.43/0.55  fof(f135,plain,(
% 1.43/0.55    v1_relat_1(k2_funct_1(sK2)) | ~spl7_5),
% 1.43/0.55    inference(avatar_component_clause,[],[f133])).
% 1.43/0.55  fof(f133,plain,(
% 1.43/0.55    spl7_5 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.43/0.55  fof(f184,plain,(
% 1.43/0.55    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl7_10),
% 1.43/0.55    inference(resolution,[],[f178,f55])).
% 1.43/0.55  fof(f55,plain,(
% 1.43/0.55    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f29])).
% 1.43/0.55  fof(f29,plain,(
% 1.43/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.43/0.55    inference(flattening,[],[f28])).
% 1.43/0.55  fof(f28,plain,(
% 1.43/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.43/0.55    inference(ennf_transformation,[],[f19])).
% 1.43/0.55  fof(f19,axiom,(
% 1.43/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.43/0.55  fof(f178,plain,(
% 1.43/0.55    v1_funct_1(k2_funct_1(sK2)) | ~spl7_10),
% 1.43/0.55    inference(avatar_component_clause,[],[f176])).
% 1.43/0.55  fof(f176,plain,(
% 1.43/0.55    spl7_10 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.43/0.55  fof(f279,plain,(
% 1.43/0.55    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_10 | ~spl7_22)),
% 1.43/0.55    inference(backward_demodulation,[],[f189,f278])).
% 1.43/0.55  fof(f189,plain,(
% 1.43/0.55    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_10)),
% 1.43/0.55    inference(forward_demodulation,[],[f188,f162])).
% 1.43/0.55  fof(f188,plain,(
% 1.43/0.55    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_5 | ~spl7_6 | ~spl7_10)),
% 1.43/0.55    inference(forward_demodulation,[],[f187,f151])).
% 1.43/0.55  % (28285)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.55  fof(f187,plain,(
% 1.43/0.55    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | (~spl7_5 | ~spl7_10)),
% 1.43/0.55    inference(subsumption_resolution,[],[f183,f135])).
% 1.43/0.55  fof(f183,plain,(
% 1.43/0.55    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl7_10),
% 1.43/0.55    inference(resolution,[],[f178,f54])).
% 1.43/0.55  % (28279)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.55  fof(f54,plain,(
% 1.43/0.55    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f29])).
% 1.43/0.55  fof(f155,plain,(
% 1.43/0.55    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl7_1 | ~spl7_6)),
% 1.43/0.55    inference(subsumption_resolution,[],[f41,f154])).
% 1.43/0.55  fof(f154,plain,(
% 1.43/0.55    v1_funct_1(k2_funct_1(sK2)) | (~spl7_1 | ~spl7_6)),
% 1.43/0.55    inference(subsumption_resolution,[],[f113,f138])).
% 1.43/0.55  fof(f113,plain,(
% 1.43/0.55    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl7_1),
% 1.43/0.55    inference(resolution,[],[f105,f57])).
% 1.43/0.55  fof(f57,plain,(
% 1.43/0.55    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f31])).
% 1.43/0.55  fof(f31,plain,(
% 1.43/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.43/0.55    inference(flattening,[],[f30])).
% 1.43/0.55  fof(f30,plain,(
% 1.43/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.43/0.55    inference(ennf_transformation,[],[f12])).
% 1.43/0.55  fof(f12,axiom,(
% 1.43/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.43/0.55  fof(f41,plain,(
% 1.43/0.55    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.43/0.55    inference(cnf_transformation,[],[f23])).
% 1.43/0.55  fof(f23,plain,(
% 1.43/0.55    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.43/0.55    inference(flattening,[],[f22])).
% 1.43/0.55  fof(f22,plain,(
% 1.43/0.55    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.43/0.55    inference(ennf_transformation,[],[f21])).
% 1.43/0.55  fof(f21,negated_conjecture,(
% 1.43/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.43/0.55    inference(negated_conjecture,[],[f20])).
% 1.43/0.55  fof(f20,conjecture,(
% 1.43/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.43/0.55  fof(f478,plain,(
% 1.43/0.55    k1_xboole_0 != sK2 | k1_xboole_0 != sK0 | v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 1.43/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.43/0.55  fof(f477,plain,(
% 1.43/0.55    ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_12 | ~spl7_14 | ~spl7_18 | ~spl7_23 | spl7_33),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f476])).
% 1.43/0.55  fof(f476,plain,(
% 1.43/0.55    $false | (~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_12 | ~spl7_14 | ~spl7_18 | ~spl7_23 | spl7_33)),
% 1.43/0.55    inference(subsumption_resolution,[],[f475,f359])).
% 1.43/0.55  fof(f359,plain,(
% 1.43/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_12 | ~spl7_14 | ~spl7_18 | ~spl7_23)),
% 1.43/0.55    inference(forward_demodulation,[],[f358,f95])).
% 1.43/0.55  fof(f95,plain,(
% 1.43/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.43/0.55    inference(equality_resolution,[],[f75])).
% 1.43/0.55  fof(f75,plain,(
% 1.43/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f6])).
% 1.43/0.55  fof(f6,axiom,(
% 1.43/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.43/0.55  fof(f358,plain,(
% 1.43/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | (~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_12 | ~spl7_14 | ~spl7_18 | ~spl7_23)),
% 1.43/0.55    inference(forward_demodulation,[],[f357,f49])).
% 1.43/0.55  fof(f49,plain,(
% 1.43/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.43/0.55    inference(cnf_transformation,[],[f10])).
% 1.43/0.55  fof(f10,axiom,(
% 1.43/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.43/0.55  fof(f357,plain,(
% 1.43/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)))) | (~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_12 | ~spl7_14 | ~spl7_18 | ~spl7_23)),
% 1.43/0.55    inference(forward_demodulation,[],[f356,f333])).
% 1.43/0.55  fof(f333,plain,(
% 1.43/0.55    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_18 | ~spl7_23)),
% 1.43/0.55    inference(subsumption_resolution,[],[f331,f332])).
% 1.43/0.55  fof(f332,plain,(
% 1.43/0.55    k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl7_6 | ~spl7_11 | ~spl7_18 | ~spl7_23)),
% 1.43/0.55    inference(forward_demodulation,[],[f316,f48])).
% 1.43/0.55  % (28275)Refutation not found, incomplete strategy% (28275)------------------------------
% 1.43/0.55  % (28275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (28275)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (28275)Memory used [KB]: 6396
% 1.43/0.55  % (28275)Time elapsed: 0.133 s
% 1.43/0.55  % (28275)------------------------------
% 1.43/0.55  % (28275)------------------------------
% 1.43/0.55  fof(f48,plain,(
% 1.43/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.43/0.55    inference(cnf_transformation,[],[f10])).
% 1.43/0.55  fof(f316,plain,(
% 1.43/0.55    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl7_6 | ~spl7_11 | ~spl7_18 | ~spl7_23)),
% 1.43/0.55    inference(backward_demodulation,[],[f234,f304])).
% 1.43/0.55  fof(f304,plain,(
% 1.43/0.55    k1_xboole_0 = sK2 | (~spl7_6 | ~spl7_11 | ~spl7_23)),
% 1.43/0.55    inference(subsumption_resolution,[],[f157,f293])).
% 1.43/0.55  fof(f293,plain,(
% 1.43/0.55    k1_xboole_0 = k2_relat_1(sK2) | (~spl7_11 | ~spl7_23)),
% 1.43/0.55    inference(backward_demodulation,[],[f196,f269])).
% 1.43/0.55  fof(f269,plain,(
% 1.43/0.55    k1_xboole_0 = sK1 | ~spl7_23),
% 1.43/0.55    inference(avatar_component_clause,[],[f267])).
% 1.43/0.55  fof(f267,plain,(
% 1.43/0.55    spl7_23 <=> k1_xboole_0 = sK1),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.43/0.55  fof(f196,plain,(
% 1.43/0.55    sK1 = k2_relat_1(sK2) | ~spl7_11),
% 1.43/0.55    inference(avatar_component_clause,[],[f194])).
% 1.43/0.55  fof(f194,plain,(
% 1.43/0.55    spl7_11 <=> sK1 = k2_relat_1(sK2)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.43/0.55  fof(f157,plain,(
% 1.43/0.55    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl7_6),
% 1.43/0.55    inference(resolution,[],[f138,f53])).
% 1.43/0.55  fof(f53,plain,(
% 1.43/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.43/0.55    inference(cnf_transformation,[],[f27])).
% 1.43/0.55  fof(f27,plain,(
% 1.43/0.55    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.43/0.55    inference(flattening,[],[f26])).
% 1.43/0.55  fof(f26,plain,(
% 1.43/0.55    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.43/0.55    inference(ennf_transformation,[],[f11])).
% 1.43/0.55  fof(f11,axiom,(
% 1.43/0.55    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.43/0.55  fof(f234,plain,(
% 1.43/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl7_18),
% 1.43/0.55    inference(avatar_component_clause,[],[f232])).
% 1.43/0.55  fof(f232,plain,(
% 1.43/0.55    spl7_18 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.43/0.55  fof(f331,plain,(
% 1.43/0.55    k1_xboole_0 != k2_relat_1(k2_funct_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_23)),
% 1.43/0.55    inference(forward_demodulation,[],[f311,f304])).
% 1.43/0.55  fof(f311,plain,(
% 1.43/0.55    k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k2_funct_1(sK2)) | (~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_23)),
% 1.43/0.55    inference(backward_demodulation,[],[f165,f304])).
% 1.43/0.55  fof(f165,plain,(
% 1.43/0.55    k1_xboole_0 != k2_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_funct_1(sK2) | ~spl7_5),
% 1.43/0.55    inference(resolution,[],[f135,f53])).
% 1.43/0.55  fof(f356,plain,(
% 1.43/0.55    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0))))) | (~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_12 | ~spl7_14 | ~spl7_18 | ~spl7_23)),
% 1.43/0.55    inference(forward_demodulation,[],[f322,f333])).
% 1.43/0.55  fof(f322,plain,(
% 1.43/0.55    m1_subset_1(k2_funct_1(k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(k1_xboole_0))),k2_relat_1(k2_funct_1(k2_funct_1(k1_xboole_0)))))) | (~spl7_6 | ~spl7_11 | ~spl7_12 | ~spl7_14 | ~spl7_23)),
% 1.43/0.55    inference(backward_demodulation,[],[f246,f304])).
% 1.43/0.55  fof(f246,plain,(
% 1.43/0.55    m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(sK2))),k2_relat_1(k2_funct_1(k2_funct_1(sK2)))))) | (~spl7_12 | ~spl7_14)),
% 1.43/0.55    inference(subsumption_resolution,[],[f242,f202])).
% 1.43/0.55  fof(f202,plain,(
% 1.43/0.55    v1_relat_1(k2_funct_1(k2_funct_1(sK2))) | ~spl7_12),
% 1.43/0.55    inference(avatar_component_clause,[],[f200])).
% 1.43/0.55  fof(f200,plain,(
% 1.43/0.55    spl7_12 <=> v1_relat_1(k2_funct_1(k2_funct_1(sK2)))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.43/0.55  fof(f242,plain,(
% 1.43/0.55    ~v1_relat_1(k2_funct_1(k2_funct_1(sK2))) | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(sK2))),k2_relat_1(k2_funct_1(k2_funct_1(sK2)))))) | ~spl7_14),
% 1.43/0.55    inference(resolution,[],[f212,f55])).
% 1.43/0.55  fof(f212,plain,(
% 1.43/0.55    v1_funct_1(k2_funct_1(k2_funct_1(sK2))) | ~spl7_14),
% 1.43/0.55    inference(avatar_component_clause,[],[f210])).
% 1.43/0.55  fof(f210,plain,(
% 1.43/0.55    spl7_14 <=> v1_funct_1(k2_funct_1(k2_funct_1(sK2)))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.43/0.55  fof(f475,plain,(
% 1.43/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl7_33),
% 1.43/0.55    inference(forward_demodulation,[],[f474,f96])).
% 1.43/0.55  fof(f96,plain,(
% 1.43/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.43/0.55    inference(equality_resolution,[],[f74])).
% 1.43/0.55  fof(f74,plain,(
% 1.43/0.55    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f6])).
% 1.43/0.55  fof(f474,plain,(
% 1.43/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl7_33),
% 1.43/0.55    inference(subsumption_resolution,[],[f473,f48])).
% 1.43/0.55  fof(f473,plain,(
% 1.43/0.55    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl7_33),
% 1.43/0.55    inference(superposition,[],[f462,f83])).
% 1.43/0.55  fof(f462,plain,(
% 1.43/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | spl7_33),
% 1.43/0.55    inference(avatar_component_clause,[],[f460])).
% 1.43/0.55  fof(f460,plain,(
% 1.43/0.55    spl7_33 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 1.43/0.55  fof(f467,plain,(
% 1.43/0.55    ~spl7_33 | spl7_34 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_12 | ~spl7_14 | ~spl7_18 | ~spl7_23 | spl7_29),
% 1.43/0.55    inference(avatar_split_clause,[],[f441,f431,f267,f232,f210,f200,f194,f137,f133,f464,f460])).
% 1.43/0.55  fof(f464,plain,(
% 1.43/0.55    spl7_34 <=> k1_xboole_0 = sK0),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 1.43/0.55  fof(f431,plain,(
% 1.43/0.55    spl7_29 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 1.43/0.55  fof(f441,plain,(
% 1.43/0.55    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | (~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_12 | ~spl7_14 | ~spl7_18 | ~spl7_23 | spl7_29)),
% 1.43/0.55    inference(subsumption_resolution,[],[f440,f359])).
% 1.43/0.55  fof(f440,plain,(
% 1.43/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | spl7_29),
% 1.43/0.55    inference(forward_demodulation,[],[f439,f96])).
% 1.43/0.55  fof(f439,plain,(
% 1.43/0.55    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl7_29),
% 1.43/0.55    inference(resolution,[],[f433,f89])).
% 1.43/0.55  fof(f89,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f40])).
% 1.43/0.55  fof(f40,plain,(
% 1.43/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.55    inference(flattening,[],[f39])).
% 1.43/0.55  fof(f39,plain,(
% 1.43/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.55    inference(ennf_transformation,[],[f17])).
% 1.43/0.55  fof(f17,axiom,(
% 1.43/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.43/0.55  fof(f433,plain,(
% 1.43/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | spl7_29),
% 1.43/0.55    inference(avatar_component_clause,[],[f431])).
% 1.43/0.55  fof(f451,plain,(
% 1.43/0.55    spl7_31 | ~spl7_6 | ~spl7_11 | ~spl7_23),
% 1.43/0.55    inference(avatar_split_clause,[],[f304,f267,f194,f137,f448])).
% 1.43/0.55  fof(f448,plain,(
% 1.43/0.55    spl7_31 <=> k1_xboole_0 = sK2),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 1.43/0.55  fof(f434,plain,(
% 1.43/0.55    ~spl7_29 | ~spl7_5 | ~spl7_6 | spl7_9 | ~spl7_11 | ~spl7_18 | ~spl7_23),
% 1.43/0.55    inference(avatar_split_clause,[],[f381,f267,f232,f194,f171,f137,f133,f431])).
% 1.43/0.55  fof(f171,plain,(
% 1.43/0.55    spl7_9 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.43/0.55  fof(f381,plain,(
% 1.43/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (~spl7_5 | ~spl7_6 | spl7_9 | ~spl7_11 | ~spl7_18 | ~spl7_23)),
% 1.43/0.55    inference(forward_demodulation,[],[f380,f333])).
% 1.43/0.55  fof(f380,plain,(
% 1.43/0.55    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (~spl7_6 | spl7_9 | ~spl7_11 | ~spl7_23)),
% 1.43/0.55    inference(forward_demodulation,[],[f379,f304])).
% 1.43/0.55  fof(f379,plain,(
% 1.43/0.55    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl7_9 | ~spl7_23)),
% 1.43/0.55    inference(forward_demodulation,[],[f173,f269])).
% 1.43/0.55  fof(f173,plain,(
% 1.43/0.55    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl7_9),
% 1.43/0.55    inference(avatar_component_clause,[],[f171])).
% 1.43/0.55  fof(f424,plain,(
% 1.43/0.55    spl7_27 | ~spl7_3 | ~spl7_6 | ~spl7_11 | ~spl7_23),
% 1.43/0.55    inference(avatar_split_clause,[],[f324,f267,f194,f137,f121,f421])).
% 1.43/0.55  fof(f421,plain,(
% 1.43/0.55    spl7_27 <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.43/0.55  fof(f121,plain,(
% 1.43/0.55    spl7_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.43/0.55  fof(f324,plain,(
% 1.43/0.55    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl7_3 | ~spl7_6 | ~spl7_11 | ~spl7_23)),
% 1.43/0.55    inference(backward_demodulation,[],[f287,f304])).
% 1.43/0.55  fof(f287,plain,(
% 1.43/0.55    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl7_3 | ~spl7_23)),
% 1.43/0.55    inference(backward_demodulation,[],[f123,f269])).
% 1.43/0.55  fof(f123,plain,(
% 1.43/0.55    v1_funct_2(sK2,sK0,sK1) | ~spl7_3),
% 1.43/0.55    inference(avatar_component_clause,[],[f121])).
% 1.43/0.55  fof(f303,plain,(
% 1.43/0.55    ~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | spl7_8 | ~spl7_10 | ~spl7_23),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f302])).
% 1.43/0.55  fof(f302,plain,(
% 1.43/0.55    $false | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | spl7_8 | ~spl7_10 | ~spl7_23)),
% 1.43/0.55    inference(subsumption_resolution,[],[f301,f300])).
% 1.43/0.55  fof(f300,plain,(
% 1.43/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl7_8 | ~spl7_23)),
% 1.43/0.55    inference(forward_demodulation,[],[f290,f96])).
% 1.43/0.55  fof(f290,plain,(
% 1.43/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl7_8 | ~spl7_23)),
% 1.43/0.55    inference(backward_demodulation,[],[f169,f269])).
% 1.43/0.55  fof(f169,plain,(
% 1.43/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl7_8),
% 1.43/0.55    inference(avatar_component_clause,[],[f167])).
% 1.43/0.55  fof(f167,plain,(
% 1.43/0.55    spl7_8 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.43/0.55  fof(f301,plain,(
% 1.43/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_10 | ~spl7_23)),
% 1.43/0.55    inference(forward_demodulation,[],[f292,f96])).
% 1.43/0.55  fof(f292,plain,(
% 1.43/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_10 | ~spl7_23)),
% 1.43/0.55    inference(backward_demodulation,[],[f192,f269])).
% 1.43/0.55  fof(f270,plain,(
% 1.43/0.55    spl7_22 | spl7_23 | ~spl7_3),
% 1.43/0.55    inference(avatar_split_clause,[],[f126,f121,f267,f263])).
% 1.43/0.55  fof(f126,plain,(
% 1.43/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_3),
% 1.43/0.55    inference(subsumption_resolution,[],[f125,f44])).
% 1.43/0.55  fof(f44,plain,(
% 1.43/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.43/0.55    inference(cnf_transformation,[],[f23])).
% 1.43/0.55  fof(f125,plain,(
% 1.43/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 1.43/0.55    inference(resolution,[],[f123,f90])).
% 1.43/0.55  fof(f90,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f40])).
% 1.43/0.55  fof(f235,plain,(
% 1.43/0.55    spl7_18 | ~spl7_1 | ~spl7_2 | ~spl7_6),
% 1.43/0.55    inference(avatar_split_clause,[],[f151,f137,f108,f103,f232])).
% 1.43/0.55  fof(f213,plain,(
% 1.43/0.55    spl7_14 | ~spl7_5 | ~spl7_10),
% 1.43/0.55    inference(avatar_split_clause,[],[f186,f176,f133,f210])).
% 1.43/0.55  fof(f186,plain,(
% 1.43/0.55    v1_funct_1(k2_funct_1(k2_funct_1(sK2))) | (~spl7_5 | ~spl7_10)),
% 1.43/0.55    inference(subsumption_resolution,[],[f182,f135])).
% 1.43/0.55  fof(f182,plain,(
% 1.43/0.55    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) | ~spl7_10),
% 1.43/0.55    inference(resolution,[],[f178,f57])).
% 1.43/0.55  fof(f203,plain,(
% 1.43/0.55    spl7_12 | ~spl7_5 | ~spl7_10),
% 1.43/0.55    inference(avatar_split_clause,[],[f185,f176,f133,f200])).
% 1.43/0.55  fof(f185,plain,(
% 1.43/0.55    v1_relat_1(k2_funct_1(k2_funct_1(sK2))) | (~spl7_5 | ~spl7_10)),
% 1.43/0.55    inference(subsumption_resolution,[],[f181,f135])).
% 1.43/0.55  fof(f181,plain,(
% 1.43/0.55    ~v1_relat_1(k2_funct_1(sK2)) | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) | ~spl7_10),
% 1.43/0.55    inference(resolution,[],[f178,f56])).
% 1.43/0.55  fof(f56,plain,(
% 1.43/0.55    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f31])).
% 1.43/0.55  fof(f197,plain,(
% 1.43/0.55    spl7_11 | ~spl7_4 | ~spl7_7),
% 1.43/0.55    inference(avatar_split_clause,[],[f160,f142,f128,f194])).
% 1.43/0.55  fof(f179,plain,(
% 1.43/0.55    spl7_10 | ~spl7_1 | ~spl7_6),
% 1.43/0.55    inference(avatar_split_clause,[],[f154,f137,f103,f176])).
% 1.43/0.55  fof(f174,plain,(
% 1.43/0.55    ~spl7_8 | ~spl7_9 | ~spl7_1 | ~spl7_6),
% 1.43/0.55    inference(avatar_split_clause,[],[f155,f137,f103,f171,f167])).
% 1.43/0.55  fof(f149,plain,(
% 1.43/0.55    ~spl7_4 | spl7_6),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f148])).
% 1.43/0.55  fof(f148,plain,(
% 1.43/0.55    $false | (~spl7_4 | spl7_6)),
% 1.43/0.55    inference(subsumption_resolution,[],[f130,f146])).
% 1.43/0.55  fof(f146,plain,(
% 1.43/0.55    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_6),
% 1.43/0.55    inference(resolution,[],[f139,f82])).
% 1.43/0.55  fof(f82,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f36])).
% 1.43/0.55  fof(f36,plain,(
% 1.43/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.55    inference(ennf_transformation,[],[f14])).
% 1.43/0.55  fof(f14,axiom,(
% 1.43/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.43/0.55  fof(f139,plain,(
% 1.43/0.55    ~v1_relat_1(sK2) | spl7_6),
% 1.43/0.55    inference(avatar_component_clause,[],[f137])).
% 1.43/0.55  fof(f145,plain,(
% 1.43/0.55    spl7_7),
% 1.43/0.55    inference(avatar_split_clause,[],[f46,f142])).
% 1.43/0.55  fof(f46,plain,(
% 1.43/0.55    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.43/0.55    inference(cnf_transformation,[],[f23])).
% 1.43/0.55  fof(f140,plain,(
% 1.43/0.55    spl7_5 | ~spl7_6 | ~spl7_1),
% 1.43/0.55    inference(avatar_split_clause,[],[f112,f103,f137,f133])).
% 1.43/0.55  fof(f112,plain,(
% 1.43/0.55    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl7_1),
% 1.43/0.55    inference(resolution,[],[f105,f56])).
% 1.43/0.55  fof(f131,plain,(
% 1.43/0.55    spl7_4),
% 1.43/0.55    inference(avatar_split_clause,[],[f44,f128])).
% 1.43/0.55  fof(f124,plain,(
% 1.43/0.55    spl7_3),
% 1.43/0.55    inference(avatar_split_clause,[],[f43,f121])).
% 1.43/0.55  fof(f43,plain,(
% 1.43/0.55    v1_funct_2(sK2,sK0,sK1)),
% 1.43/0.55    inference(cnf_transformation,[],[f23])).
% 1.43/0.55  fof(f111,plain,(
% 1.43/0.55    spl7_2),
% 1.43/0.55    inference(avatar_split_clause,[],[f45,f108])).
% 1.43/0.55  fof(f45,plain,(
% 1.43/0.55    v2_funct_1(sK2)),
% 1.43/0.55    inference(cnf_transformation,[],[f23])).
% 1.43/0.55  fof(f106,plain,(
% 1.43/0.55    spl7_1),
% 1.43/0.55    inference(avatar_split_clause,[],[f42,f103])).
% 1.43/0.55  fof(f42,plain,(
% 1.43/0.55    v1_funct_1(sK2)),
% 1.43/0.55    inference(cnf_transformation,[],[f23])).
% 1.43/0.55  % SZS output end Proof for theBenchmark
% 1.43/0.55  % (28291)------------------------------
% 1.43/0.55  % (28291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (28291)Termination reason: Refutation
% 1.43/0.55  
% 1.43/0.55  % (28291)Memory used [KB]: 11129
% 1.43/0.55  % (28291)Time elapsed: 0.126 s
% 1.43/0.55  % (28291)------------------------------
% 1.43/0.55  % (28291)------------------------------
% 1.43/0.55  % (28295)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.55  % (28279)Refutation not found, incomplete strategy% (28279)------------------------------
% 1.43/0.55  % (28279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (28279)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (28279)Memory used [KB]: 10746
% 1.43/0.55  % (28279)Time elapsed: 0.149 s
% 1.43/0.55  % (28279)------------------------------
% 1.43/0.55  % (28279)------------------------------
% 1.43/0.56  % (28270)Success in time 0.195 s
%------------------------------------------------------------------------------
